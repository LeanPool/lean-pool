/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.ScalarSecondPartial
public import LeanPool.FastDynamo.Local.PonomarenkoCrossNormalizedRadialODE
public import LeanPool.FastDynamo.Local.PonomarenkoCartesianInteriorDerivative
public import LeanPool.FastDynamo.Local.PonomarenkoExteriorSecondDerivative
public import LeanPool.FastDynamo.Local.PolarHessianCalculus
public import LeanPool.FastDynamo.Local.PonomarenkoRealRadialBridge

/-!
# Polar Laplacian formulas for the Cartesian Ponomarenko mode

This module proves a generic punctured-plane formula for the Cartesian second partials and the
Laplacian of the angular modes `b(r)` and `q^2 b(r)`, where `r = ‖y‖` and
`q = (y₁+i y₂)/r`, with the result expressed through the polar radial operator
`realPolarRadialOperator`.  It also records that the interior Ponomarenko circular branches are
entire, and that real restrictions of complex-analytic functions have the expected real
derivatives.  `Local/HorizontalModeSecondDerivatives.lean` and
`Local/HorizontalModeExteriorSecondDerivatives.lean` apply these formulas to the regular and
decaying branches of the two-component mode of `lem:jump-horizontal-mode`.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace PonomarenkoCartesianPolarLaplacian

open Complex Filter Set
open CartesianRadialRegularity
open PonomarenkoOriginProfiles
open ComplexRadius
open PonomarenkoCartesianExteriorDerivative
open PonomarenkoCartesianExteriorSecondDerivative
open PonomarenkoExteriorSecondDerivative
open PonomarenkoCartesianInteriorDerivative
open PonomarenkoRealRadialBridge
open PonomarenkoCrossNormalizedJump
open PolarHessianCalculus
open ScalarSecondPartial

/-! ## Generic scalar angular modes -/

/-- The scalar radial mode obtained by evaluating `b` at the Euclidean radius. -/
def radialMode (b : ℝ → ℂ) (y : WholePlane) : ℂ :=
  b ‖y‖

/-- The angular-frequency-two scalar mode `q² b(r)` on the punctured plane. -/
def phaseSqRadialMode (b : ℝ → ℂ) (y : WholePlane) : ℂ :=
  exteriorPhase y ^ 2 * b ‖y‖

/-- The explicit `j`-th Cartesian first partial of a radial mode away from the axis. -/
def radialModeFirstPartial (b : ℝ → ℂ) (j : Fin 2) (y : WholePlane) : ℂ :=
  (radiusDerivative y (wholePlaneBasis j) : ℂ) * deriv b ‖y‖

/-- The explicit `j`-th Cartesian first partial of the mode `q² b(r)`. -/
def phaseSqRadialModeFirstPartial
    (b : ℝ → ℂ) (j : Fin 2) (y : WholePlane) : ℂ :=
  2 * exteriorPhase y * exteriorPhaseDerivative y (wholePlaneBasis j) * b ‖y‖ +
    exteriorPhase y ^ 2 * (radiusDerivative y (wholePlaneBasis j) : ℂ) * deriv b ‖y‖

/-- The algebraic ordered second-partial value for `q² b(r)` from polar product rules. -/
def phaseSqRadialModeSecondPartialValue
    (b b' b'' : ℂ) (y : WholePlane) (j k : Fin 2) : ℂ :=
  phaseSquareRadialProductSecondPartialValue b b' b'' y j k

/-- Identification of a Fréchet directional derivative with a one-variable derivative along the
coordinate line through `y` in direction `e_k`, by uniqueness of the derivative. -/
private theorem fderiv_eq_of_coordinateLine_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : WholePlane → E} {y : WholePlane} {k : Fin 2} {v : E}
    (hp : DifferentiableAt ℝ p y)
    (hline : HasDerivAt (fun t : ℝ ↦ p (coordinateLine y k t)) v 0) :
    fderiv ℝ p y (wholePlaneBasis k) = v := by
  have hcomp := hp.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (coordinateLine_hasDerivAt y k 0) (coordinateLine_zero y k).symm
  change HasDerivAt (p ∘ coordinateLine y k)
    (fderiv ℝ p y (wholePlaneBasis k)) 0 at hcomp
  change HasDerivAt (p ∘ coordinateLine y k) v 0 at hline
  exact hcomp.unique hline

/-- Away from the polar axis, the `j`-th Cartesian partial of the radial mode `b(‖y‖)` is
`(∂_j‖y‖) b'(‖y‖)`. -/
theorem fderiv_radialMode_basis
    {b : ℝ → ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hb : HasDerivAt b (deriv b ‖y‖) ‖y‖) (j : Fin 2) :
    fderiv ℝ (radialMode b) y (wholePlaneBasis j) =
      radialModeFirstPartial b j y := by
  have h := hb.hasFDerivAt.comp y (radius_hasFDerivAt hy)
  have h' := h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)
  change HasFDerivAt (radialMode b) _ y at h'
  rw [h'.fderiv]
  simp [radialModeFirstPartial, radiusDerivative_apply,
    inner_wholePlaneBasis, Complex.real_smul]

/-- Away from the polar axis, the `j`-th Cartesian partial of the angular-frequency-two mode
`q² b(‖y‖)` is `2q(∂_j q)b(‖y‖) + q²(∂_j‖y‖)b'(‖y‖)`. -/
theorem fderiv_phaseSqRadialMode_basis
    {b : ℝ → ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hb : HasDerivAt b (deriv b ‖y‖) ‖y‖) (j : Fin 2) :
    fderiv ℝ (phaseSqRadialMode b) y (wholePlaneBasis j) =
      phaseSqRadialModeFirstPartial b j y := by
  have hq := exteriorPhase_hasFDerivAt hy
  have hbcomp := hb.hasFDerivAt.comp y (radius_hasFDerivAt hy)
  have h := (hq.pow 2).mul hbcomp
  have h' := h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)
  change HasFDerivAt (phaseSqRadialMode b) _ y at h'
  rw [h'.fderiv]
  simp [phaseSqRadialModeFirstPartial,
    radiusDerivative_apply, inner_wholePlaneBasis, Complex.real_smul]
  ring

/-- Restricted to the coordinate line through `y` in direction `e_k`, the `j`-th first partial of a
radial mode is differentiable at the base point, with the explicit polar second-partial value. -/
theorem radialModeFirstPartial_coordinateLine_hasDerivAt
    {b : ℝ → ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hb'' : HasDerivAt (deriv b) (deriv (deriv b) ‖y‖) ‖y‖)
    (j k : Fin 2) :
    HasDerivAt (fun t : ℝ ↦ radialModeFirstPartial b j (coordinateLine y k t))
      (radialCompositionSecondPartialValue
        (deriv b ‖y‖) (deriv (deriv b) ‖y‖) y j k) 0 := by
  simpa [radialModeFirstPartial, Complex.real_smul] using
    radialCompositionPartial_coordinateLine_hasDerivAt hy hb'' j k

/-- Restricted to the coordinate line through `y` in direction `e_k`, the `j`-th first partial of
the mode `q² b(r)` is differentiable at the base point, with the explicit polar second-partial
value supplied by `PolarHessianCalculus`. -/
theorem phaseSqRadialModeFirstPartial_coordinateLine_hasDerivAt
    {b : ℝ → ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hb : HasDerivAt b (deriv b ‖y‖) ‖y‖)
    (hb'' : HasDerivAt (deriv b) (deriv (deriv b) ‖y‖) ‖y‖)
    (j k : Fin 2) :
    HasDerivAt
      (fun t : ℝ ↦ phaseSqRadialModeFirstPartial b j (coordinateLine y k t))
      (phaseSqRadialModeSecondPartialValue
        (b ‖y‖) (deriv b ‖y‖) (deriv (deriv b) ‖y‖) y j k) 0 := by
  have hq := exteriorPhase_coordinateLine_hasDerivAt hy k
  have hqj := exteriorPhasePartial_coordinateLine_hasDerivAt hy j k
  have hbline := radialComposition_coordinateLine_hasDerivAt hy hb k
  have hrjR := radiusPartial_coordinateLine_hasDerivAt hy j k
  have hrj : HasDerivAt
      (fun t : ℝ ↦
        (radiusDerivative (coordinateLine y k t) (wholePlaneBasis j) : ℂ))
      (radiusSecondPartial y j k : ℂ) 0 := by
    have h := hrjR.smul_const (1 : ℂ)
    convert! h using 1 <;> simp [Complex.real_smul]
  have hdb := hb''.scomp_of_eq 0 (radius_coordinateLine_hasDerivAt hy k) (by simp)
  have hfirst := (((hq.mul hqj).mul hbline).const_mul 2)
  have hsecond := (((hq.pow 2).mul hrj).mul hdb)
  have h := hfirst.add hsecond
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · simp only [phaseSqRadialModeFirstPartial, Pi.add_apply, Pi.mul_apply,
      Pi.pow_apply, Function.comp_apply]
    ring
  · simp only [phaseSqRadialModeSecondPartialValue,
      phaseSquareRadialProductSecondPartialValue,
      exteriorPhaseSquareSecondPartial, radialCompositionSecondPartialValue,
      coordinateLine_zero, Pi.mul_apply, Pi.pow_apply,
      Function.comp_apply, Complex.real_smul]
    push_cast
    ring

/-- Away from the polar axis, the complexified partial `y ↦ ∂_j‖y‖ = y_j/‖y‖` is differentiable. -/
private theorem radiusDerivative_basis_differentiableAt
    {y : WholePlane} (hy : y ≠ 0) (j : Fin 2) :
    DifferentiableAt ℝ
      (fun x : WholePlane ↦ (radiusDerivative x (wholePlaneBasis j) : ℂ)) y := by
  have hcoord : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : WholePlane ↦ x j) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.of_le le_top
  have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : WholePlane ↦ ‖x‖) y :=
    contDiffAt_norm ℝ hy
  have hreal : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : WholePlane ↦ x j / ‖x‖) y :=
    hcoord.div hnorm (norm_ne_zero_iff.mpr hy)
  have hofReal : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℝ ↦ (r : ℂ)) (y j / ‖y‖) :=
    Complex.ofRealCLM.contDiff.contDiffAt.of_le le_top
  have hc := ContDiffAt.fun_comp y (g := fun r : ℝ ↦ (r : ℂ)) hofReal hreal
  have hd := hc.differentiableAt (by simp)
  simpa only [radiusDerivative_apply, inner_wholePlaneBasis] using hd

/-- Away from the polar axis, the explicit `j`-th first partial of a radial mode is differentiable,
given that `b'` is differentiable at the radius. -/
private theorem radialModeFirstPartial_differentiableAt
    {b : ℝ → ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hb'' : HasDerivAt (deriv b) (deriv (deriv b) ‖y‖) ‖y‖)
    (j : Fin 2) : DifferentiableAt ℝ (radialModeFirstPartial b j) y := by
  have hrj : DifferentiableAt ℝ
      (fun x : WholePlane ↦ (radiusDerivative x (wholePlaneBasis j) : ℂ)) y := by
    exact radiusDerivative_basis_differentiableAt hy j
  have hdb : DifferentiableAt ℝ (fun x : WholePlane ↦ deriv b ‖x‖) y :=
    hb''.differentiableAt.comp y (radius_hasFDerivAt hy).differentiableAt
  exact hrj.mul hdb

/-- Away from the polar axis, the partial derivative `y ↦ ∂_j q(y)` of the angular phase is
differentiable. -/
private theorem phaseDerivative_basis_differentiableAt
    {y : WholePlane} (hy : y ≠ 0) (j : Fin 2) :
    DifferentiableAt ℝ
      (fun x : WholePlane ↦ exteriorPhaseDerivative x (wholePlaneBasis j)) y := by
  have hphase : ContDiffAt ℝ (⊤ : ℕ∞) exteriorPhase y :=
    PonomarenkoExteriorSecondDerivative.exteriorPhase_contDiffAt_infty hy
  have hfderiv : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ exteriorPhase) y :=
    hphase.fderiv_right (by simp)
  have happly : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : WholePlane ↦ fderiv ℝ exteriorPhase x (wholePlaneBasis j)) y :=
    hfderiv.clm_apply contDiffAt_const
  have hevent :
      (fun x : WholePlane ↦ fderiv ℝ exteriorPhase x (wholePlaneBasis j)) =ᶠ[nhds y]
        fun x : WholePlane ↦ exteriorPhaseDerivative x (wholePlaneBasis j) := by
    have hyc : y ∈ ({0} : Set WholePlane)ᶜ := by simpa using hy
    filter_upwards [isOpen_compl_singleton.mem_nhds hyc] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    rw [(exteriorPhase_hasFDerivAt hx0).fderiv]
  exact (happly.congr_of_eventuallyEq hevent.symm).differentiableAt (by simp)

/-- Away from the polar axis, the explicit `j`-th first partial of the mode `q² b(r)` is
differentiable, given differentiability of `b` and `b'` at the radius. -/
private theorem phaseSqRadialModeFirstPartial_differentiableAt
    {b : ℝ → ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hb : HasDerivAt b (deriv b ‖y‖) ‖y‖)
    (hb'' : HasDerivAt (deriv b) (deriv (deriv b) ‖y‖) ‖y‖)
    (j : Fin 2) : DifferentiableAt ℝ (phaseSqRadialModeFirstPartial b j) y := by
  have hq := (exteriorPhase_hasFDerivAt hy).differentiableAt
  have hqj := phaseDerivative_basis_differentiableAt hy j
  have hbcomp : DifferentiableAt ℝ (fun x : WholePlane ↦ b ‖x‖) y :=
    hb.differentiableAt.comp y (radius_hasFDerivAt hy).differentiableAt
  have hrj : DifferentiableAt ℝ
      (fun x : WholePlane ↦ (radiusDerivative x (wholePlaneBasis j) : ℂ)) y := by
    exact radiusDerivative_basis_differentiableAt hy j
  have hdb : DifferentiableAt ℝ (fun x : WholePlane ↦ deriv b ‖x‖) y :=
    hb''.differentiableAt.comp y (radius_hasFDerivAt hy).differentiableAt
  unfold phaseSqRadialModeFirstPartial
  have hfirst : DifferentiableAt ℝ
      (fun x : WholePlane ↦
        2 * exteriorPhase x * exteriorPhaseDerivative x (wholePlaneBasis j) * b ‖x‖) y := by
    convert! (((hq.mul hqj).mul hbcomp).const_mul (2 : ℂ)) using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hsecond : DifferentiableAt ℝ
      (fun x : WholePlane ↦ exteriorPhase x ^ 2 *
        (radiusDerivative x (wholePlaneBasis j) : ℂ) * deriv b ‖x‖) y := by
    convert! (((hq.pow 2).mul hrj).mul hdb) using 1
  exact hfirst.add hsecond

/-- Off the polar axis, the ordered second Cartesian partial of a radial mode `b(‖y‖)` equals the
explicit polar expression in `b'(‖y‖)` and `b''(‖y‖)`. -/
theorem scalarSecondPartial_radialMode
    {b : ℝ → ℂ}
    (hb : ∀ r : ℝ, 0 < r → HasDerivAt b (deriv b r) r)
    (hb'' : ∀ r : ℝ, 0 < r → HasDerivAt (deriv b) (deriv (deriv b) r) r)
    {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    scalarSecondPartial (radialMode b) j k y =
      radialCompositionSecondPartialValue
        (deriv b ‖y‖) (deriv (deriv b) ‖y‖) y j k := by
  have hevent :
      (fun x : WholePlane ↦ fderiv ℝ (radialMode b) x (wholePlaneBasis j)) =ᶠ[nhds y]
        radialModeFirstPartial b j := by
    have hyc : y ∈ ({0} : Set WholePlane)ᶜ := by simpa using hy
    filter_upwards [isOpen_compl_singleton.mem_nhds hyc] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact fderiv_radialMode_basis hx0 (hb ‖x‖ (norm_pos_iff.mpr hx0)) j
  unfold scalarSecondPartial
  rw [hevent.fderiv_eq]
  exact fderiv_eq_of_coordinateLine_hasDerivAt
    (radialModeFirstPartial_differentiableAt hy
      (hb'' ‖y‖ (norm_pos_iff.mpr hy)) j)
    (radialModeFirstPartial_coordinateLine_hasDerivAt hy
      (hb'' ‖y‖ (norm_pos_iff.mpr hy)) j k)

/-- Off the polar axis, the ordered second Cartesian partial of `q² b(‖y‖)` equals the explicit
polar expression in `b(‖y‖)`, `b'(‖y‖)` and `b''(‖y‖)`. -/
theorem scalarSecondPartial_phaseSqRadialMode
    {b : ℝ → ℂ}
    (hb : ∀ r : ℝ, 0 < r → HasDerivAt b (deriv b r) r)
    (hb'' : ∀ r : ℝ, 0 < r → HasDerivAt (deriv b) (deriv (deriv b) r) r)
    {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    scalarSecondPartial (phaseSqRadialMode b) j k y =
      phaseSqRadialModeSecondPartialValue
        (b ‖y‖) (deriv b ‖y‖) (deriv (deriv b) ‖y‖) y j k := by
  have hevent :
      (fun x : WholePlane ↦ fderiv ℝ (phaseSqRadialMode b) x (wholePlaneBasis j)) =ᶠ[nhds y]
        phaseSqRadialModeFirstPartial b j := by
    have hyc : y ∈ ({0} : Set WholePlane)ᶜ := by simpa using hy
    filter_upwards [isOpen_compl_singleton.mem_nhds hyc] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact fderiv_phaseSqRadialMode_basis hx0
      (hb ‖x‖ (norm_pos_iff.mpr hx0)) j
  unfold scalarSecondPartial
  rw [hevent.fderiv_eq]
  exact fderiv_eq_of_coordinateLine_hasDerivAt
    (phaseSqRadialModeFirstPartial_differentiableAt hy
      (hb ‖y‖ (norm_pos_iff.mpr hy))
      (hb'' ‖y‖ (norm_pos_iff.mpr hy)) j)
    (phaseSqRadialModeFirstPartial_coordinateLine_hasDerivAt hy
      (hb ‖y‖ (norm_pos_iff.mpr hy))
      (hb'' ‖y‖ (norm_pos_iff.mpr hy)) j k)

/-! ## Generic trace formulas -/

/-- Trace of the polar Hessian for a radial mode: `Δ_⊥ (b(r)) = b'' + r⁻¹ b'`, the order-zero
Bessel operator of Paper Lemma 2.1. -/
theorem scalarCartesianLaplacian_radialMode
    {b : ℝ → ℂ}
    (hb : ∀ r : ℝ, 0 < r → HasDerivAt b (deriv b r) r)
    (hb'' : ∀ r : ℝ, 0 < r → HasDerivAt (deriv b) (deriv (deriv b) r) r)
    {y : WholePlane} (hy : y ≠ 0) :
    scalarCartesianLaplacian (radialMode b) y =
      deriv (deriv b) ‖y‖ + ((1 / ‖y‖ : ℝ) : ℂ) * deriv b ‖y‖ := by
  rw [scalarCartesianLaplacian,
    scalarSecondPartial_radialMode hb hb'' hy,
    scalarSecondPartial_radialMode hb hb'' hy,
    radialCompositionSecondPartialValue_trace hy]
  simp [Complex.real_smul]

/-- Trace of the explicit polar second-partial values for the mode `q² b(r)`:
`q²(b'' + r⁻¹b' - 4r⁻²b)`, the order-two operator produced by the angular factor `e^{2iθ}`. -/
theorem phaseSqRadialModeSecondPartialValue_trace
    {y : WholePlane} (hy : y ≠ 0) (b b' b'' : ℂ) :
    phaseSqRadialModeSecondPartialValue b b' b'' y 0 0 +
        phaseSqRadialModeSecondPartialValue b b' b'' y 1 1 =
      exteriorPhase y ^ 2 *
        (b'' + ((1 / ‖y‖ : ℝ) : ℂ) * b' -
          4 / complexRadius y ^ 2 * b) := by
  unfold phaseSqRadialModeSecondPartialValue
  rw [phaseSquareRadialProductSecondPartialValue_trace hy]
  simp only [Complex.real_smul]
  ring

/-- Off the polar axis, `Δ_⊥ (q² b(r)) = q²(b'' + r⁻¹b' - 4r⁻²b)`: the angular-frequency-two mode
solves the order-two radial operator of Paper Lemma 2.1 (`ν₊ = 2`). -/
theorem scalarCartesianLaplacian_phaseSqRadialMode
    {b : ℝ → ℂ}
    (hb : ∀ r : ℝ, 0 < r → HasDerivAt b (deriv b r) r)
    (hb'' : ∀ r : ℝ, 0 < r → HasDerivAt (deriv b) (deriv (deriv b) r) r)
    {y : WholePlane} (hy : y ≠ 0) :
    scalarCartesianLaplacian (phaseSqRadialMode b) y =
      exteriorPhase y ^ 2 *
        (deriv (deriv b) ‖y‖ + ((1 / ‖y‖ : ℝ) : ℂ) * deriv b ‖y‖ -
          4 / complexRadius y ^ 2 * b ‖y‖) := by
  rw [scalarCartesianLaplacian,
    scalarSecondPartial_phaseSqRadialMode hb hb'' hy,
    scalarSecondPartial_phaseSqRadialMode hb hb'' hy,
    phaseSqRadialModeSecondPartialValue_trace hy]

/-! ## Analytic real restrictions of the interior transverse branches -/

/-- The interior plus branch is entire in the radial variable. -/
theorem plusInside_analyticAt (kappa r : ℂ) :
    AnalyticAt ℂ (plusInside kappa) r := by
  have hinner : AnalyticAt ℂ (fun s : ℂ ↦ kappa * s) r :=
    analyticAt_const.mul analyticAt_id
  unfold plusInside
  convert! analyticAt_const.mul
    ((ModifiedBessel.I2_analyticAt (kappa * r)).comp hinner) using 1

/-- The interior minus branch is entire in the radial variable. -/
theorem minusInside_analyticAt (kappa r : ℂ) :
    AnalyticAt ℂ (minusInside kappa) r := by
  have hinner : AnalyticAt ℂ (fun s : ℂ ↦ kappa * s) r :=
    analyticAt_const.mul analyticAt_id
  unfold minusInside
  convert! analyticAt_const.mul
    ((ModifiedBessel.I0_analyticAt (kappa * r)).comp hinner) using 1

/-- The restriction of a complex-analytic function to the real axis is
real-analytic. -/
theorem realRestriction_analyticAt
    {f : ℂ → ℂ} {r : ℝ} (hf : AnalyticAt ℂ f (r : ℂ)) :
    AnalyticAt ℝ (fun s : ℝ ↦ f (s : ℂ)) r := by
  exact hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt r)

/-- A real restriction of a complex-analytic function is differentiable with its
own derivative. -/
theorem realRestriction_hasDerivAt_self
    {f : ℂ → ℂ} {r : ℝ} (hf : AnalyticAt ℂ f (r : ℂ)) :
    HasDerivAt (fun s : ℝ ↦ f (s : ℂ))
      (deriv (fun s : ℝ ↦ f (s : ℂ)) r) r :=
  (realRestriction_analyticAt hf).differentiableAt.hasDerivAt

/-- The derivative of a real restriction is again differentiable with its own
derivative. -/
theorem realRestriction_deriv_hasDerivAt_self
    {f : ℂ → ℂ} {r : ℝ} (hf : AnalyticAt ℂ f (r : ℂ)) :
    HasDerivAt (deriv (fun s : ℝ ↦ f (s : ℂ)))
      (deriv (deriv (fun s : ℝ ↦ f (s : ℂ))) r) r :=
  (realRestriction_analyticAt hf).deriv.differentiableAt.hasDerivAt

/-- The second real derivative of a real restriction is the restriction of the
second complex derivative. -/
theorem deriv_deriv_realRestriction_eq
    {f : ℂ → ℂ} {r : ℝ} (hf : AnalyticAt ℂ f (r : ℂ)) :
    deriv (deriv (fun s : ℝ ↦ f (s : ℂ))) r =
      deriv (deriv f) (r : ℂ) := by
  have heventComplex : ∀ᶠ z : ℂ in nhds (r : ℂ), AnalyticAt ℂ f z :=
    hf.eventually_analyticAt
  have heventReal : ∀ᶠ s : ℝ in nhds r, AnalyticAt ℂ f (s : ℂ) :=
    Complex.continuous_ofReal.continuousAt heventComplex
  have heq :
      deriv (fun s : ℝ ↦ f (s : ℂ)) =ᶠ[nhds r]
        fun s : ℝ ↦ deriv f (s : ℂ) := by
    filter_upwards [heventReal] with s hs
    exact deriv_realRestriction_eq hs.differentiableAt
  have hsecond : HasDerivAt (fun s : ℝ ↦ deriv f (s : ℂ))
      (deriv (deriv f) (r : ℂ)) r :=
    hasDerivAt_realRestriction hf.deriv.differentiableAt.hasDerivAt
  exact (hsecond.congr_of_eventuallyEq heq).deriv

/-- The unphased radial operator appearing after taking a polar Laplacian trace. -/
def realPolarRadialOperator (orderSq : ℂ) (b : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv (deriv b) r + ((1 / r : ℝ) : ℂ) * deriv b r -
    orderSq / (r : ℂ) ^ 2 * b r

end PonomarenkoCartesianPolarLaplacian
end FastDynamo

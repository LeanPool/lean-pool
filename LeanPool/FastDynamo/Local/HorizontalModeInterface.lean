/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalModeBulkIdentity

/-!
# The unit-circle interface densities of the horizontal Ponomarenko mode

This module carries out the interface step (the third of the three steps listed in
`Local/HorizontalModeEigenpair.lean`) of the weak eigenvalue equation in the proof of
`lem:jump-horizontal-mode` (`eq:transmission-horizontal` and the closing paragraph): the
cancellation of the two coordinate interface densities of the pivot field

`D_j = ∂_j b + b_j V⁰_⊥`,   `V⁰_⊥ = 1_{r<1} Ω r e_θ`.

Differentiating `D_j` in the `j`-th coordinate direction produces the unit-circle density
`n_j [D_j]` with `n = y` the outward unit normal (the `unitCircleJumpDensity` of
`Analysis/WholePlaneUnitDiskFibreDerivativeSource.lean`).  Summing over `j` gives the singular
part

`[∂_r b] - Ω b_r e_θ`,

and `eq:transmission-horizontal` makes it vanish.  In the cross-normalized parametrization the
computation is completely explicit:

* the two branches of the mode restricted to a radial ray with frozen phase `q = e^{iθ}` are
  `((B_- + q²B_+)/2, i(B_- - q²B_+)/2)`, so the Cartesian normal-derivative jump is the same
  circular combination of the scalar jumps `[B_±']`;
* those scalar jumps are the cross-normalized Wronskian values `[B_+'] = -1`,
  `[B_-'] = 1`;
* the normal component of the boundary trace is `b·n = q B_r(1)`;
* the transmission law `[B_θ'] = Ω B_r(1)` of `TransverseInterfaceLaws`, together with the
  `[B_θ'] = i`, is the boundary identity `Ω B_r(1) = i`, which is exactly what
  turns `(q B_r(1)) Ω e_θ` into the circular jump vector.

Nothing here is distributional: only pointwise identities on the unit circle, plus the
continuity and integrability needed to feed the density into the surface functional.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace HorizontalMode

open Complex Filter MeasureTheory Metric Set Topology
open CartesianRadialRegularity
open ModifiedBesselBoundaryBehavior
open PonomarenkoCartesianExteriorDerivative
open ComplexRadius
open PonomarenkoOriginProfiles
open PonomarenkoCrossNormalizedJump
open PonomarenkoFreeOmegaInterface
open PonomarenkoRealRadialBridge
open WholePlaneFibreSource

/-! ## Elementary coordinate algebra on `ℂ²` -/

/-- A real scalar acting on a complex scalar multiple is the product of the two scalars. -/
private theorem real_smul_complex_smul_c2 (r : ℝ) (c : ℂ) (v : C2) :
    r • (c • v) = ((r : ℂ) * c) • v := by
  apply PiLp.ext
  intro i
  simp [Complex.real_smul, mul_assoc]

/-- Every transverse vector is the sum of its two coordinates times the coordinate basis. -/
private theorem wholePlane_eq_coordinate_smul_basis' (y : WholePlane) :
    y = y 0 • wholePlaneBasis 0 + y 1 • wholePlaneBasis 1 := by
  ext j
  fin_cases j <;> simp [wholePlaneBasis]

/-- A real-linear map into `ℂ²` evaluated on `y` is the coordinate-weighted sum of its values
on the coordinate basis.  This is the passage from coordinate derivatives to the normal
derivative. -/
theorem sum_coordinate_smul_c2_clm (A : WholePlane →L[ℝ] C2) (y : WholePlane) :
    (y 0) • A (wholePlaneBasis 0) + (y 1) • A (wholePlaneBasis 1) = A y := by
  conv_rhs => rw [wholePlane_eq_coordinate_smul_basis' y]
  rw [map_add, map_smul, map_smul]

/-! ## The circular amplitude and the radial rays -/

/-- The Cartesian pair attached to a frozen phase `q` and a pair of circular amplitudes:
`b₁ = (M + q²P)/2`, `b₂ = i(M - q²P)/2`, the two-component form of
`b₁ + ib₂ = q²B₊`, `b₁ - ib₂ = B₋` (last paragraph of the proof of
`lem:jump-horizontal-mode`). -/
def horizontalCircularAmplitude (q P M : ℂ) : C2 :=
  WithLp.toLp 2 ![(M + q ^ 2 * P) / 2, I * (M - q ^ 2 * P) / 2]

/-- First component of the circular amplitude. -/
@[simp] theorem horizontalCircularAmplitude_apply_zero (q P M : ℂ) :
    horizontalCircularAmplitude q P M 0 = (M + q ^ 2 * P) / 2 := by
  simp [horizontalCircularAmplitude]

/-- Second component of the circular amplitude. -/
@[simp] theorem horizontalCircularAmplitude_apply_one (q P M : ℂ) :
    horizontalCircularAmplitude q P M 1 = I * (M - q ^ 2 * P) / 2 := by
  simp [horizontalCircularAmplitude]

/-- Squared radius along a ray through a unit vector. -/
private theorem squaredRadius_smul_of_norm_one {z : WholePlane} (hz : ‖z‖ = 1) (r : ℝ) :
    squaredRadius (r • z) = r ^ 2 := by
  rw [squaredRadius, norm_smul, hz, Real.norm_eq_abs, mul_one, sq_abs]

/-- Complex coordinate along a ray. -/
private theorem complexCoordinate_smul (r : ℝ) (z : WholePlane) :
    complexCoordinate (r • z) = (r : ℂ) * complexCoordinate z := by
  simp only [complexCoordinate, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- The interior branch along a radial ray through a unit vector is the circular amplitude of
the two regular scalar branches, with the phase frozen at `q = complexCoordinate z`. -/
theorem horizontalInteriorField_smul_eq_circularAmplitude
    (kappa : ℂ) {z : WholePlane} (hz : ‖z‖ = 1) (r : ℝ) :
    horizontalInteriorField kappa (r • z) =
      horizontalCircularAmplitude (complexCoordinate z)
        (plusInside kappa (r : ℂ)) (minusInside kappa (r : ℂ)) := by
  have hsq : squaredRadius (r • z) = r ^ 2 := squaredRadius_smul_of_norm_one hz r
  have hcast : (((r ^ 2 : ℝ)) : ℂ) = ((r : ℂ)) ^ 2 := by push_cast; ring
  have hminus : radialScalar (minusOriginProfile kappa) (r • z) =
      minusInside kappa (r : ℂ) := by
    rw [radialScalar, minusOriginProfile, hsq, hcast,
      minusInside_origin_factorization]
  have hplus : degreeTwoFactor (plusOriginProfile kappa) (r • z) =
      complexCoordinate z ^ 2 * plusInside kappa (r : ℂ) := by
    rw [degreeTwoFactor, radialScalar, plusOriginProfile, hsq, hcast,
      complexCoordinate_smul, plusInside_origin_factorization]
    ring
  have h0 : horizontalInteriorField kappa (r • z) 0 =
      horizontalCircularAmplitude (complexCoordinate z)
        (plusInside kappa (r : ℂ)) (minusInside kappa (r : ℂ)) 0 := by
    rw [horizontalInteriorField_apply_zero, horizontalCircularAmplitude_apply_zero,
      hminus, hplus]
  have h1 : horizontalInteriorField kappa (r • z) 1 =
      horizontalCircularAmplitude (complexCoordinate z)
        (plusInside kappa (r : ℂ)) (minusInside kappa (r : ℂ)) 1 := by
    rw [horizontalInteriorField_apply_one, horizontalCircularAmplitude_apply_one,
      hminus, hplus]
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

/-- The exterior branch along a radial ray through a unit vector, at positive radius, is the
circular amplitude of the two decaying scalar branches with the same frozen phase. -/
theorem horizontalExteriorField_smul_eq_circularAmplitude
    (kappa : ℂ) {z : WholePlane} (hz : ‖z‖ = 1) {r : ℝ} (hr : 0 < r) :
    horizontalExteriorField kappa (r • z) =
      horizontalCircularAmplitude (complexCoordinate z)
        (plusOutside kappa (r : ℂ)) (minusOutside kappa (r : ℂ)) := by
  have hradius : complexRadius (r • z) = (r : ℂ) := by
    rw [complexRadius, norm_smul, hz, Real.norm_eq_abs, mul_one, abs_of_pos hr]
  have hrne : ((r : ℂ)) ≠ 0 := by
    simpa using ne_of_gt hr
  have hphase : exteriorPhase (r • z) = complexCoordinate z := by
    rw [exteriorPhase, hradius, complexCoordinate_smul]
    field_simp
  have h0 : horizontalExteriorField kappa (r • z) 0 =
      horizontalCircularAmplitude (complexCoordinate z)
        (plusOutside kappa (r : ℂ)) (minusOutside kappa (r : ℂ)) 0 := by
    rw [horizontalExteriorField_apply_zero, horizontalCircularAmplitude_apply_zero,
      hradius, hphase]
  have h1 : horizontalExteriorField kappa (r • z) 1 =
      horizontalCircularAmplitude (complexCoordinate z)
        (plusOutside kappa (r : ℂ)) (minusOutside kappa (r : ℂ)) 1 := by
    rw [horizontalExteriorField_apply_one, horizontalCircularAmplitude_apply_one,
      hradius, hphase]
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

/-! ## The normal derivative of each branch along a ray -/

/-- The scaling map `r ↦ r • z` has derivative `z` at every radius. -/
private theorem hasDerivAt_smul_right (z : WholePlane) (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ s • z) z r := by
  simpa using (hasDerivAt_id r).smul_const z

/-- Differentiating the interior branch along the ray through `z` gives its Fréchet derivative
applied to `z`. -/
theorem hasDerivAt_horizontalInteriorField_ray (kappa : ℂ) (z : WholePlane) :
    HasDerivAt (fun r : ℝ ↦ horizontalInteriorField kappa (r • z))
      (fderiv ℝ (horizontalInteriorField kappa) z z) 1 := by
  have hdiff : HasFDerivAt (horizontalInteriorField kappa)
      (fderiv ℝ (horizontalInteriorField kappa) z) ((1 : ℝ) • z) := by
    rw [one_smul]
    exact ((horizontalInteriorField_contDiff kappa).differentiable (by simp) z).hasFDerivAt
  simpa [Function.comp_def] using hdiff.comp_hasDerivAt 1 (hasDerivAt_smul_right z 1)

/-- Differentiating the exterior branch along the ray through a nonzero `z` gives its Fréchet
derivative applied to `z`. -/
theorem hasDerivAt_horizontalExteriorField_ray
    {kappa : ℂ} (hkappa : 0 < kappa.re) {z : WholePlane} (hz : z ≠ 0) :
    HasDerivAt (fun r : ℝ ↦ horizontalExteriorField kappa (r • z))
      (horizontalExteriorFieldDerivative kappa z z) 1 := by
  have hdiff : HasFDerivAt (horizontalExteriorField kappa)
      (horizontalExteriorFieldDerivative kappa z) ((1 : ℝ) • z) := by
    rw [one_smul]
    exact horizontalExteriorField_hasFDerivAt hkappa hz
  simpa [Function.comp_def] using hdiff.comp_hasDerivAt 1 (hasDerivAt_smul_right z 1)

/-- Component projection of a `ℂ²`-valued real derivative. -/
private theorem hasDerivAt_component {F : ℝ → C2} {D : C2} {r : ℝ} (a : Fin 2)
    (hF : HasDerivAt F D r) :
    HasDerivAt (fun s : ℝ ↦ F s a) (D a) r := by
  have hproj : HasFDerivAt (fun v : C2 ↦ v a)
      (((EuclideanSpace.proj (𝕜 := ℂ) a).restrictScalars ℝ :
        C2 →L[ℝ] ℂ)) (F r) :=
    ((EuclideanSpace.proj (𝕜 := ℂ) a).restrictScalars ℝ).hasFDerivAt
  exact hproj.comp_hasDerivAt r hF

/-! ## The Cartesian normal-derivative jump on the unit circle -/

/-- On the unit circle the two coordinates satisfy `y₀² + y₁² = 1`, as complex numbers. -/
theorem coordinate_sq_add_sq_of_norm_one {z : WholePlane} (hz : ‖z‖ = 1) :
    ((z 0 : ℂ)) ^ 2 + ((z 1 : ℂ)) ^ 2 = 1 := by
  have hsqR : z 0 ^ 2 + z 1 ^ 2 = 1 := by
    rw [← squaredRadius_eq_coordinate_squares, squaredRadius, hz, one_pow]
  have hcast : (((z 0 ^ 2 + z 1 ^ 2 : ℝ)) : ℂ) = ((1 : ℝ) : ℂ) := by rw [hsqR]
  push_cast at hcast
  exact hcast

/-- On the unit circle the phase `q = y₀ + i y₁` is a unit complex number, in the algebraic
form `q (y₀ - i y₁) = 1`. -/
theorem complexCoordinate_mul_conj_of_norm_one {z : WholePlane} (hz : ‖z‖ = 1) :
    complexCoordinate z * ((z 0 : ℂ) - I * (z 1 : ℂ)) = 1 := by
  have hsqC := coordinate_sq_add_sq_of_norm_one hz
  unfold complexCoordinate
  linear_combination hsqC - ((z 1 : ℂ)) ^ 2 * Complex.I_mul_I

/-- On the unit circle the phase is nonzero. -/
theorem complexCoordinate_ne_zero_of_norm_one {z : WholePlane} (hz : ‖z‖ = 1) :
    complexCoordinate z ≠ 0 :=
  left_ne_zero_of_mul_eq_one (complexCoordinate_mul_conj_of_norm_one hz)

/-- The Cartesian normal-derivative jump of the two-component mode on the unit circle is the
circular combination of the two cross-normalized Wronskian jumps
`[B₊'] = -1` and `[B₋'] = 1`.  No interface law is used. -/
theorem horizontalRadialDerivativeJump
    {kappa : ℂ} (hkappa : 0 < kappa.re) {z : WholePlane} (hz : ‖z‖ = 1) :
    horizontalExteriorFieldDerivative kappa z z -
        fderiv ℝ (horizontalInteriorField kappa) z z =
      horizontalCircularAmplitude (complexCoordinate z) (-1) 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    norm_num at hz
  set q : ℂ := complexCoordinate z with hq
  set Din : C2 := fderiv ℝ (horizontalInteriorField kappa) z z with hDin
  set Dout : C2 := horizontalExteriorFieldDerivative kappa z z with hDout
  have hqne : q ≠ 0 := complexCoordinate_ne_zero_of_norm_one hz
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hqne
  -- the two rays, in circular-amplitude form
  have hIn : HasDerivAt
      (fun r : ℝ ↦ horizontalCircularAmplitude q
        (plusInside kappa (r : ℂ)) (minusInside kappa (r : ℂ))) Din 1 := by
    refine (hasDerivAt_horizontalInteriorField_ray kappa z).congr_of_eventuallyEq ?_
    filter_upwards [] with r
    exact (horizontalInteriorField_smul_eq_circularAmplitude kappa hz r).symm
  have hOut : HasDerivAt
      (fun r : ℝ ↦ horizontalCircularAmplitude q
        (plusOutside kappa (r : ℂ)) (minusOutside kappa (r : ℂ))) Dout 1 := by
    refine (hasDerivAt_horizontalExteriorField_ray hkappa hz0).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with r hr
    exact (horizontalExteriorField_smul_eq_circularAmplitude kappa hz hr).symm
  -- extract the two scalar branches from the two components
  have hminus : ∀ (P M : ℂ → ℂ) (D : C2),
      HasDerivAt (fun r : ℝ ↦ horizontalCircularAmplitude q (P (r : ℂ)) (M (r : ℂ))) D 1 →
      HasDerivAt (fun r : ℝ ↦ M (r : ℂ)) (D 0 - I * D 1) 1 := by
    intro P M D hD
    have h0 := hasDerivAt_component 0 hD
    have h1 := hasDerivAt_component 1 hD
    refine (h0.sub (h1.const_mul I)).congr_of_eventuallyEq ?_
    filter_upwards [] with r
    simp only [Pi.sub_apply, horizontalCircularAmplitude_apply_zero,
      horizontalCircularAmplitude_apply_one]
    linear_combination ((M (r : ℂ) - q ^ 2 * P (r : ℂ)) / 2) * Complex.I_mul_I
  have hplus : ∀ (P M : ℂ → ℂ) (D : C2),
      HasDerivAt (fun r : ℝ ↦ horizontalCircularAmplitude q (P (r : ℂ)) (M (r : ℂ))) D 1 →
      HasDerivAt (fun r : ℝ ↦ P (r : ℂ)) ((q ^ 2)⁻¹ * (D 0 + I * D 1)) 1 := by
    intro P M D hD
    have h0 := hasDerivAt_component 0 hD
    have h1 := hasDerivAt_component 1 hD
    have hscaled : HasDerivAt (fun r : ℝ ↦ q ^ 2 * P (r : ℂ)) (D 0 + I * D 1) 1 := by
      refine (h0.add (h1.const_mul I)).congr_of_eventuallyEq ?_
      filter_upwards [] with r
      simp only [Pi.add_apply, horizontalCircularAmplitude_apply_zero,
        horizontalCircularAmplitude_apply_one]
      linear_combination (-(M (r : ℂ) - q ^ 2 * P (r : ℂ)) / 2) * Complex.I_mul_I
    refine (hscaled.const_mul (q ^ 2)⁻¹).congr_of_eventuallyEq ?_
    filter_upwards [] with r
    field_simp
  have hMinusIn := hminus (plusInside kappa) (minusInside kappa) Din hIn
  have hMinusOut := hminus (plusOutside kappa) (minusOutside kappa) Dout hOut
  have hPlusIn := hplus (plusInside kappa) (minusInside kappa) Din hIn
  have hPlusOut := hplus (plusOutside kappa) (minusOutside kappa) Dout hOut
  -- the two scalar Wronskian jumps
  have hjumpMinus : (Dout 0 - I * Dout 1) - (Din 0 - I * Din 1) = 1 := by
    rw [← hMinusOut.deriv, ← hMinusIn.deriv]
    exact minus_realDerivativeJump hkappa
  have hjumpPlus : (q ^ 2)⁻¹ * (Dout 0 + I * Dout 1) -
      (q ^ 2)⁻¹ * (Din 0 + I * Din 1) = -1 := by
    rw [← hPlusOut.deriv, ← hPlusIn.deriv]
    exact plus_realDerivativeJump hkappa
  have hjumpPlus' : (Dout 0 + I * Dout 1) - (Din 0 + I * Din 1) = -q ^ 2 := by
    field_simp at hjumpPlus
    linear_combination hjumpPlus
  -- solve the two-by-two system componentwise
  have h0 : (Dout - Din) 0 = horizontalCircularAmplitude q (-1) 1 0 := by
    rw [horizontalCircularAmplitude_apply_zero]
    have hsub : (Dout - Din) 0 = Dout 0 - Din 0 := rfl
    rw [hsub]
    linear_combination (1 / 2 : ℂ) * hjumpMinus + (1 / 2 : ℂ) * hjumpPlus'
  have h1 : (Dout - Din) 1 = horizontalCircularAmplitude q (-1) 1 1 := by
    rw [horizontalCircularAmplitude_apply_one]
    have hsub : (Dout - Din) 1 = Dout 1 - Din 1 := rfl
    rw [hsub]
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination (I / 2 : ℂ) * hjumpMinus - (I / 2 : ℂ) * hjumpPlus' +
      (Dout 1 - Din 1) * hI
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

/-! ## The normal component of the boundary trace -/

/-- On the unit circle the complex-bilinear normal component of the mode is the phased radial
boundary amplitude `b·n = q B_r(1)` (with `B_r = (B₊ + B₋)/2` as in the proof of
`lem:jump-horizontal-mode`). -/
theorem horizontalInteriorField_normalComponent
    (kappa : ℂ) {z : WholePlane} (hz : ‖z‖ = 1) :
    (z 0 : ℂ) * horizontalInteriorField kappa z 0 +
        (z 1 : ℂ) * horizontalInteriorField kappa z 1 =
      complexCoordinate z * radialInside kappa 1 := by
  have hray := horizontalInteriorField_smul_eq_circularAmplitude kappa hz 1
  rw [one_smul, Complex.ofReal_one] at hray
  have hconj := complexCoordinate_mul_conj_of_norm_one hz
  have hqdef : complexCoordinate z = (z 0 : ℂ) + I * (z 1 : ℂ) := rfl
  have h0 : horizontalInteriorField kappa z 0 =
      (minusInside kappa 1 + complexCoordinate z ^ 2 * plusInside kappa 1) / 2 := by
    rw [hray, horizontalCircularAmplitude_apply_zero]
  have h1 : horizontalInteriorField kappa z 1 =
      I * (minusInside kappa 1 - complexCoordinate z ^ 2 * plusInside kappa 1) / 2 := by
    rw [hray, horizontalCircularAmplitude_apply_one]
  rw [h0, h1, radialInside]
  linear_combination (-(minusInside kappa 1) / 2) * hqdef +
    (complexCoordinate z * plusInside kappa 1 / 2) * hconj

/-! ## The transmission identity of the transverse screw velocity

The transverse part `V⁰_⊥ = Ω r e_θ = (-Ω y₂, Ω y₁)` of the interior screw flow
(`eq:jump-flow`) is
`horizontalInteriorTransverseVelocity` of `Local/HorizontalModeBulkIdentity.lean`, where it is
built as the restriction of a real-linear map so that the Leibniz rule needs no case analysis.
-/

/-- The paper's transmission law `[B_θ'] = Ω B_r(1)` of `eq:transmission-horizontal`,
combined with the cross-normalized value `[B_θ'] = i`, is the denominator-free
boundary identity `Ω B_r(1) = i`. -/
theorem omega_mul_radialInside_one_of_interfaceLaws
    {Omega : ℝ} {kappa : ℂ} (hkappa : 0 < kappa.re)
    (laws : TransverseInterfaceLaws (Omega : ℂ) kappa) :
    (Omega : ℂ) * radialInside kappa 1 = I :=
  laws.angular_derivative_jump.symm.trans (angular_boundaryDerivativeJump hkappa)

/-- On the unit circle, `q² - 1 = 2i y₂ q`; this converts the angular part of the circular
reconstruction into the Cartesian component `-Ω y₂` of the screw velocity. -/
theorem complexCoordinate_sq_sub_one_of_norm_one {z : WholePlane} (hz : ‖z‖ = 1) :
    complexCoordinate z ^ 2 - 1 = 2 * I * (z 1 : ℂ) * complexCoordinate z := by
  have hsqC := coordinate_sq_add_sq_of_norm_one hz
  unfold complexCoordinate
  linear_combination hsqC - ((z 1 : ℂ)) ^ 2 * Complex.I_mul_I

/-- On the unit circle, `q² + 1 = 2 y₁ q`; this converts the radial part of the circular
reconstruction into the Cartesian component `Ω y₁` of the screw velocity. -/
theorem complexCoordinate_sq_add_one_of_norm_one {z : WholePlane} (hz : ‖z‖ = 1) :
    complexCoordinate z ^ 2 + 1 = 2 * (z 0 : ℂ) * complexCoordinate z := by
  have hsqC := coordinate_sq_add_sq_of_norm_one hz
  unfold complexCoordinate
  linear_combination -hsqC + ((z 1 : ℂ)) ^ 2 * Complex.I_mul_I

/-- The Cartesian form of `Ω b_r e_θ` at `r = 1`: the phased radial amplitude times the
transverse screw velocity is exactly the circular jump vector of `[B_±']`.  This is the
interface law `eq:transmission-horizontal` in Cartesian coordinates. -/
theorem radialAmplitude_smul_interiorTransverseVelocity
    {Omega : ℝ} {kappa : ℂ} (hOmega : (Omega : ℂ) * radialInside kappa 1 = I)
    {z : WholePlane} (hz : ‖z‖ = 1) :
    (complexCoordinate z * radialInside kappa 1) • horizontalInteriorTransverseVelocity Omega z =
      horizontalCircularAmplitude (complexCoordinate z) (-1) 1 := by
  have hsub := complexCoordinate_sq_sub_one_of_norm_one hz
  have hadd := complexCoordinate_sq_add_one_of_norm_one hz
  have h0 : ((complexCoordinate z * radialInside kappa 1) •
      horizontalInteriorTransverseVelocity Omega z) 0 =
      horizontalCircularAmplitude (complexCoordinate z) (-1) 1 0 := by
    rw [PiLp.smul_apply, smul_eq_mul, horizontalInteriorTransverseVelocity_apply_zero,
      horizontalCircularAmplitude_apply_zero]
    linear_combination (-((z 1 : ℂ)) * complexCoordinate z) * hOmega + (1 / 2 : ℂ) * hsub
  have h1 : ((complexCoordinate z * radialInside kappa 1) •
      horizontalInteriorTransverseVelocity Omega z) 1 =
      horizontalCircularAmplitude (complexCoordinate z) (-1) 1 1 := by
    rw [PiLp.smul_apply, smul_eq_mul, horizontalInteriorTransverseVelocity_apply_one,
      horizontalCircularAmplitude_apply_one]
    linear_combination ((z 0 : ℂ) * complexCoordinate z) * hOmega - (I / 2 : ℂ) * hadd
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

/-! ## The interface cancellation -/

/-- The Cartesian form of the paper's interface identity `[∂_r b] = Ω b_r e_θ` at `r = 1`
(`eq:transmission-horizontal`).  The left-hand side
is the normal contraction of the Cartesian derivative jump, the right-hand side the one-sided
stretching term of the pivot field. -/
theorem horizontalNormalDerivativeJump_eq_stretch
    {N Omega : ℝ} {kappa : ℂ} (hd : CertifiedInterfaceData N Omega kappa)
    {z : WholePlane} (hz : ‖z‖ = 1) :
    (z 0) • (horizontalExteriorPartialDerivative kappa 0 z -
          horizontalInteriorPartialDerivative kappa 0 z) +
        (z 1) • (horizontalExteriorPartialDerivative kappa 1 z -
          horizontalInteriorPartialDerivative kappa 1 z) =
      ((z 0 : ℂ) * horizontalInteriorField kappa z 0 +
          (z 1 : ℂ) * horizontalInteriorField kappa z 1) •
        horizontalInteriorTransverseVelocity Omega z := by
  have hkappa := hd.kappa_re_pos
  have hOmega := omega_mul_radialInside_one_of_interfaceLaws hkappa hd.interface_laws
  have hExtSum : (z 0) • horizontalExteriorPartialDerivative kappa 0 z +
      (z 1) • horizontalExteriorPartialDerivative kappa 1 z =
      horizontalExteriorFieldDerivative kappa z z :=
    sum_coordinate_smul_c2_clm (horizontalExteriorFieldDerivative kappa z) z
  have hIntSum : (z 0) • horizontalInteriorPartialDerivative kappa 0 z +
      (z 1) • horizontalInteriorPartialDerivative kappa 1 z =
      fderiv ℝ (horizontalInteriorField kappa) z z :=
    sum_coordinate_smul_c2_clm (fderiv ℝ (horizontalInteriorField kappa) z) z
  have hleft : (z 0) • (horizontalExteriorPartialDerivative kappa 0 z -
        horizontalInteriorPartialDerivative kappa 0 z) +
      (z 1) • (horizontalExteriorPartialDerivative kappa 1 z -
        horizontalInteriorPartialDerivative kappa 1 z) =
      horizontalExteriorFieldDerivative kappa z z -
        fderiv ℝ (horizontalInteriorField kappa) z z := by
    rw [smul_sub, smul_sub, ← hExtSum, ← hIntSum]
    abel
  rw [hleft, horizontalRadialDerivativeJump hkappa hz,
    horizontalInteriorField_normalComponent kappa hz,
    radialAmplitude_smul_interiorTransverseVelocity hOmega hz]

/-- The interface cancellation of the two coordinate source densities, for any pair of pivot
branches of the paper's shape `D_j^{in} = ∂_j b^{in} + b_j V⁰_⊥` and
`D_j^{out} = ∂_j b^{out}`.

This is step (3) of the weak-identity step of `lem:jump-horizontal-mode`: the summed density
is `[∂_r b] - Ω b_r e_θ`, which the transmission conditions annihilate. -/
theorem unitCircleJumpDensity_add_eq_zero_of_pivotBranches
    {N Omega : ℝ} {kappa : ℂ} (hd : CertifiedInterfaceData N Omega kappa)
    (pivotInterior pivotExterior : Fin 2 → WholePlane → C2)
    (hInt : ∀ (j : Fin 2) (y : WholePlane), pivotInterior j y =
      horizontalInteriorPartialDerivative kappa j y +
        horizontalInteriorField kappa y j • horizontalInteriorTransverseVelocity Omega y)
    (hExt : ∀ (j : Fin 2) (y : WholePlane), pivotExterior j y =
      horizontalExteriorPartialDerivative kappa j y)
    (y : WholePlaneUnitCircle) :
    unitCircleJumpDensity (pivotInterior 0) (pivotExterior 0) 0 y +
      unitCircleJumpDensity (pivotInterior 1) (pivotExterior 1) 1 y = 0 := by
  have hz : ‖y.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.2
  have hstep : ∀ j : Fin 2,
      unitCircleJumpDensity (pivotInterior j) (pivotExterior j) j y =
        (y.1 j) • (horizontalExteriorPartialDerivative kappa j y.1 -
            horizontalInteriorPartialDerivative kappa j y.1) -
          (((y.1 j : ℝ) : ℂ) * horizontalInteriorField kappa y.1 j) •
            horizontalInteriorTransverseVelocity Omega y.1 := by
    intro j
    change (y.1 j) • (pivotExterior j y.1 - pivotInterior j y.1) = _
    rw [hInt j y.1, hExt j y.1, sub_add_eq_sub_sub, smul_sub,
      real_smul_complex_smul_c2]
  rw [hstep 0, hstep 1]
  have hjump := horizontalNormalDerivativeJump_eq_stretch hd hz
  have hregroup :
      ((y.1 0) • (horizontalExteriorPartialDerivative kappa 0 y.1 -
            horizontalInteriorPartialDerivative kappa 0 y.1) -
          (((y.1 0 : ℝ) : ℂ) * horizontalInteriorField kappa y.1 0) •
            horizontalInteriorTransverseVelocity Omega y.1) +
        ((y.1 1) • (horizontalExteriorPartialDerivative kappa 1 y.1 -
            horizontalInteriorPartialDerivative kappa 1 y.1) -
          (((y.1 1 : ℝ) : ℂ) * horizontalInteriorField kappa y.1 1) •
            horizontalInteriorTransverseVelocity Omega y.1) =
      ((y.1 0) • (horizontalExteriorPartialDerivative kappa 0 y.1 -
            horizontalInteriorPartialDerivative kappa 0 y.1) +
          (y.1 1) • (horizontalExteriorPartialDerivative kappa 1 y.1 -
            horizontalInteriorPartialDerivative kappa 1 y.1)) -
        ((((y.1 0 : ℝ) : ℂ) * horizontalInteriorField kappa y.1 0) +
            (((y.1 1 : ℝ) : ℂ) * horizontalInteriorField kappa y.1 1)) •
          horizontalInteriorTransverseVelocity Omega y.1 := by
    rw [add_smul]
    abel
  rw [hregroup, hjump, sub_self]

end HorizontalMode
end FastDynamo

/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneFourier
public import LeanPool.FastDynamo.Local.ModifiedBesselBoundaryBehavior

/-!
# Squared-radius profiles of the interior Ponomarenko branches

The proof of `lem:jump-horizontal-mode` (Lemma 2.1) selects the `I`-branches inside the unit
disc by "regularity at the origin" (the sentence before `eq:bessel-solutions`).  Writing
`e_± = e_1 ± i e_2` and `z = y_1 + i y_2`, the two-component mode becomes
`B_- e_+ / 2 + e^{2iθ} B_+ e_- / 2`, and the power series present `B_-(r)` as a smooth function
`Φ₋(r²)` and `e^{2iθ} B_+(r)` as `z²` times a smooth function `Φ₊(r²)`, so the mode is smooth
across `r = 0`.  This module supplies the ingredients of that computation, which
`Local/HorizontalModeBranches.lean` uses to write the interior branch of the two-component
mode without dividing by the polar radius.

The scalar layer shows that the two transverse squared-radius coefficients of the interior
branches are entire, hence smooth on real squared radii, and computes their values at the
origin.  A generic calculus layer differentiates a smooth function of `|y|²` and its product
with `z²` on the whole plane.  The last part packages the real squared-radius profiles `Φ₋`,
`Φ₊` with their smoothness and their values at the origin.

No exterior, interface, Sobolev, or eigenmode claim is made here.

## Contents

* Regular squared-radius coefficients at the Ponomarenko axis: the entire hypergeometric
  building block, analyticity of the two transverse squared-radius coefficients, their real
  restrictions and smoothness, and their exact origin values.
* Cartesian regularity for squared-radius profiles: the generic radial scalar
  `radialScalar` and the degree-two factor `degreeTwoFactor`, their Fréchet derivatives,
  explicit first derivatives, values at the origin, and smoothness.
* The real squared-radius profiles `minusOriginProfile`, `plusOriginProfile`, their
  smoothness and their values at the origin.
-/

@[expose] public section

/-!
## Regular squared-radius coefficients at the Ponomarenko axis

The interior scalar branches have already been factored into powers of the polar radius
times functions of `r²`.  The two transverse coefficient functions are recorded here as
entire in their squared-radius argument, hence real analytic (and smooth) after
restriction to real squared radii.  Their exact values at the origin are also computed.

These are scalar regularity facts only.  No Cartesian extension or Sobolev claim is made
in this part.
-/

noncomputable section

namespace FastDynamo
namespace PonomarenkoOriginCoefficients

open Complex Set
open ModifiedBesselBoundaryBehavior

/-! ## Entire squared-radius coefficients -/

/-- The affine substitution `t ↦ κ² t / 4`, which carries the squared radius into the argument of
the regularized `₀F₁` series, is entire. -/
private theorem squaredRadiusArgument_analyticAt (kappa s : ℂ) :
    AnalyticAt ℂ (fun t : ℂ ↦ kappa ^ 2 * t / 4) s := by
  fun_prop

/-- The signed order-zero squared-radius coefficient is entire. -/
theorem minusInsideSquaredRadiusCoefficient_analyticAt (kappa s : ℂ) :
    AnalyticAt ℂ (minusInsideSquaredRadiusCoefficient kappa) s := by
  have hhyper : AnalyticAt ℂ
      (fun t : ℂ ↦ regularizedHGFun 0 {(1 : ℂ)} (kappa ^ 2 * t / 4)) s :=
    AnalyticAt.comp
      (g := regularizedHGFun 0 {(1 : ℂ)})
      (f := fun t : ℂ ↦ kappa ^ 2 * t / 4)
      (ModifiedBessel.regularizedHGFun_analyticAt_singleton 1 (kappa ^ 2 * s / 4))
      (squaredRadiusArgument_analyticAt kappa s)
  let f : ℂ → ℂ := fun t ↦ regularizedHGFun 0 {(1 : ℂ)} (kappa ^ 2 * t / 4)
  have hfun : minusInsideSquaredRadiusCoefficient kappa =
      (-ModifiedBessel.K0 kappa) • f := by
    funext t
    simp [minusInsideSquaredRadiusCoefficient, f]
  rw [hfun]
  exact hhyper.const_smul (c := -ModifiedBessel.K0 kappa)

/-- The order-two squared-radius coefficient is entire. -/
theorem plusInsideSquaredRadiusCoefficient_analyticAt (kappa s : ℂ) :
    AnalyticAt ℂ (plusInsideSquaredRadiusCoefficient kappa) s := by
  have hhyper : AnalyticAt ℂ
      (fun t : ℂ ↦ regularizedHGFun 0 {(3 : ℂ)} (kappa ^ 2 * t / 4)) s :=
    AnalyticAt.comp
      (g := regularizedHGFun 0 {(3 : ℂ)})
      (f := fun t : ℂ ↦ kappa ^ 2 * t / 4)
      (ModifiedBessel.regularizedHGFun_analyticAt_singleton 3 (kappa ^ 2 * s / 4))
      (squaredRadiusArgument_analyticAt kappa s)
  let f : ℂ → ℂ := fun t ↦ regularizedHGFun 0 {(3 : ℂ)} (kappa ^ 2 * t / 4)
  have hfun : plusInsideSquaredRadiusCoefficient kappa =
      (ModifiedBessel.K2 kappa * (kappa ^ 2 / 4)) • f := by
    funext t
    simp [plusInsideSquaredRadiusCoefficient, f, mul_assoc]
  rw [hfun]
  exact hhyper.const_smul (c := ModifiedBessel.K2 kappa * (kappa ^ 2 / 4))

/-! ## Real squared-radius restrictions -/

/-- The signed order-zero coefficient restricted to real squared radii is real analytic. -/
theorem minusInsideSquaredRadiusCoefficient_real_analyticAt (kappa : ℂ) (s : ℝ) :
    AnalyticAt ℝ (fun t : ℝ ↦ minusInsideSquaredRadiusCoefficient kappa (t : ℂ)) s :=
  (minusInsideSquaredRadiusCoefficient_analyticAt kappa (s : ℂ)).restrictScalars.comp
    (Complex.ofRealCLM.analyticAt s)

/-- The order-two coefficient restricted to real squared radii is real analytic. -/
theorem plusInsideSquaredRadiusCoefficient_real_analyticAt (kappa : ℂ) (s : ℝ) :
    AnalyticAt ℝ (fun t : ℝ ↦ plusInsideSquaredRadiusCoefficient kappa (t : ℂ)) s :=
  (plusInsideSquaredRadiusCoefficient_analyticAt kappa (s : ℂ)).restrictScalars.comp
    (Complex.ofRealCLM.analyticAt s)

/-- The signed order-zero coefficient is real analytic on the whole real line. -/
theorem minusInsideSquaredRadiusCoefficient_real_analyticOnNhd (kappa : ℂ) :
    AnalyticOnNhd ℝ
      (fun t : ℝ ↦ minusInsideSquaredRadiusCoefficient kappa (t : ℂ)) univ :=
  fun s _ ↦ minusInsideSquaredRadiusCoefficient_real_analyticAt kappa s

/-- The order-two coefficient is real analytic on the whole real line. -/
theorem plusInsideSquaredRadiusCoefficient_real_analyticOnNhd (kappa : ℂ) :
    AnalyticOnNhd ℝ
      (fun t : ℝ ↦ plusInsideSquaredRadiusCoefficient kappa (t : ℂ)) univ :=
  fun s _ ↦ plusInsideSquaredRadiusCoefficient_real_analyticAt kappa s

/-- The signed order-zero coefficient is `C∞` along real squared radii. -/
theorem minusInsideSquaredRadiusCoefficient_real_contDiff (kappa : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ ↦ minusInsideSquaredRadiusCoefficient kappa (t : ℂ)) :=
  (minusInsideSquaredRadiusCoefficient_real_analyticOnNhd kappa).contDiff

/-- The order-two coefficient is `C∞` along real squared radii. -/
theorem plusInsideSquaredRadiusCoefficient_real_contDiff (kappa : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ ↦ plusInsideSquaredRadiusCoefficient kappa (t : ℂ)) :=
  (plusInsideSquaredRadiusCoefficient_real_analyticOnNhd kappa).contDiff

/-! ## Exact origin values -/

/-- Value at the origin of the regularized `₀F₁` with denominator parameter `1`, the series behind
`I₀`: it equals `1`. -/
private theorem regularizedHGFun_zero_one :
    regularizedHGFun 0 {(1 : ℂ)} 0 = 1 := by
  simpa [ModifiedBessel.I0] using ModifiedBessel.I0_zero

/-- Value at the origin of the regularized `₀F₁` with denominator parameter `3`, the series behind
`I₂`: it equals `1/2`. -/
private theorem regularizedHGFun_zero_three :
    regularizedHGFun 0 {(3 : ℂ)} 0 = 1 / 2 := by
  unfold regularizedHGFun regularizedHGFunSeries
  change FormalMultilinearSeries.ofScalarsSum (E := ℂ)
    (regularizedHGFunCoeff (0 : Multiset ℂ) {(3 : ℂ)}) 0 = 1 / 2
  rw [FormalMultilinearSeries.ofScalarsSum_zero]
  norm_num [regularizedHGFunCoeff, Complex.Gamma_nat_eq_factorial]

/-- Exact axis value of the signed order-zero squared-radius coefficient. -/
@[simp] theorem minusInsideSquaredRadiusCoefficient_zero (kappa : ℂ) :
    minusInsideSquaredRadiusCoefficient kappa 0 = -ModifiedBessel.K0 kappa := by
  simp only [minusInsideSquaredRadiusCoefficient, mul_zero, zero_div]
  rw [regularizedHGFun_zero_one, mul_one]

/-- Exact axis value of the order-two squared-radius coefficient. -/
@[simp] theorem plusInsideSquaredRadiusCoefficient_zero (kappa : ℂ) :
    plusInsideSquaredRadiusCoefficient kappa 0 =
      ModifiedBessel.K2 kappa * (kappa ^ 2 / 8) := by
  simp only [plusInsideSquaredRadiusCoefficient, mul_zero, zero_div]
  rw [regularizedHGFun_zero_three]
  ring

end PonomarenkoOriginCoefficients
end FastDynamo

/-!
## Cartesian regularity for squared-radius profiles

The elementary Cartesian calculus used to remove the apparent polar
singularity of an azimuthal `m = 1` mode.  A scalar coefficient depending smoothly on
`|y|²` remains smooth on the whole transverse plane.  Multiplication by `z²`, with
`z = y₁ + i y₂`, gives the regular degree-two factor occurring in the transverse components of
the mode.

The results are generic: no Bessel functions, interface conditions, or Sobolev packaging
appear in this part.
-/

noncomputable section

namespace FastDynamo
namespace CartesianRadialRegularity

open scoped RealInnerProductSpace

/-- Squared transverse radius, used instead of the nonsmooth radius at the origin. -/
def squaredRadius (y : WholePlane) : ℝ :=
  ‖y‖ ^ 2

/-- The complex coordinate `z = y₁ + i y₂`. -/
def complexCoordinate (y : WholePlane) : ℂ :=
  (y (0 : Fin 2) : ℂ) + Complex.I * (y (1 : Fin 2) : ℂ)

/-- A scalar squared-radius profile on the Cartesian plane. -/
def radialScalar (phi : ℝ → ℂ) (y : WholePlane) : ℂ :=
  phi (squaredRadius y)

/-- The degree-two regular factor `z² phi(|y|²)`. -/
def degreeTwoFactor (phi : ℝ → ℂ) (y : WholePlane) : ℂ :=
  complexCoordinate y ^ 2 * radialScalar phi y

/-- The constant real Fréchet derivative of `complexCoordinate`. -/
def complexCoordinateCLM : WholePlane →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) : WholePlane →L[ℝ] ℝ) +
    Complex.I • (Complex.ofRealCLM.comp
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) : WholePlane →L[ℝ] ℝ))

/-- The squared transverse radius `y ↦ ‖y‖²` is smooth of every order on the whole plane, in
contrast with `‖y‖` itself, which fails to be differentiable at the origin. -/
theorem squaredRadius_contDiff :
    ContDiff ℝ (⊤ : WithTop ℕ∞) squaredRadius := by
  unfold squaredRadius
  exact contDiff_norm_sq ℝ

/-- The squared radius is the sum of the squares of the two Cartesian coordinates,
`‖y‖² = y₀² + y₁²`. -/
theorem squaredRadius_eq_coordinate_squares (y : WholePlane) :
    squaredRadius y = y (0 : Fin 2) ^ 2 + y (1 : Fin 2) ^ 2 := by
  rw [squaredRadius, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

/-- The complex coordinate `y ↦ y₀ + i y₁` is smooth of every order as a real-linear map from the
transverse plane to `ℂ`. -/
theorem complexCoordinate_contDiff :
    ContDiff ℝ (⊤ : WithTop ℕ∞) complexCoordinate := by
  unfold complexCoordinate
  have h0 : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : WholePlane ↦ (y (0 : Fin 2) : ℂ)) :=
    (Complex.ofRealCLM.comp
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) : WholePlane →L[ℝ] ℝ)).contDiff
  have h1 : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : WholePlane ↦ (y (1 : Fin 2) : ℂ)) :=
    (Complex.ofRealCLM.comp
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) : WholePlane →L[ℝ] ℝ)).contDiff
  exact h0.add (contDiff_const.mul h1)

/-- Evaluation of the continuous linear map `complexCoordinateCLM`: it sends `v` to
`v₀ + i v₁`, so it agrees with `complexCoordinate` itself. -/
@[simp] theorem complexCoordinateCLM_apply (v : WholePlane) :
    complexCoordinateCLM v =
      (v (0 : Fin 2) : ℂ) + Complex.I * (v (1 : Fin 2) : ℂ) := by
  simp [complexCoordinateCLM]

/-- The Fréchet derivative of `y ↦ ‖y‖²` at `y` is twice the inner product with `y`, i.e. the
linear form `v ↦ 2⟪y, v⟫`. -/
theorem squaredRadius_hasFDerivAt (y : WholePlane) :
    HasFDerivAt squaredRadius (2 • innerSL ℝ y) y := by
  unfold squaredRadius
  convert (hasStrictFDerivAt_norm_sq y).hasFDerivAt using 1

/-- Being real-linear, `complexCoordinate` is its own Fréchet derivative: it is differentiable at
every point with derivative the constant map `complexCoordinateCLM`. -/
theorem complexCoordinate_hasFDerivAt (y : WholePlane) :
    HasFDerivAt complexCoordinate complexCoordinateCLM y := by
  have h := complexCoordinateCLM.hasFDerivAt (x := y)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x ↦ by
    simp [complexCoordinate, complexCoordinateCLM]

/-- Chain rule for a squared-radius profile: if `phi` is differentiable at `‖y‖²` with derivative
`phi'`, then `y ↦ phi (‖y‖²)` is Fréchet differentiable at `y` with derivative
`v ↦ 2⟪y, v⟫ · phi'`. -/
theorem radialScalar_hasFDerivAt {phi : ℝ → ℂ} {phi' : ℂ}
    {y : WholePlane} (hphi : HasDerivAt phi phi' (squaredRadius y)) :
    HasFDerivAt (radialScalar phi)
      ((2 • innerSL ℝ y).smulRight phi') y := by
  have hout : HasFDerivAt phi
      ((1 : ℝ →L[ℝ] ℝ).smulRight phi') (squaredRadius y) := hphi
  have h := hout.comp y (squaredRadius_hasFDerivAt y)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x ↦ rfl

/-- Differentiability of the degree-two regular factor `z² phi(‖y‖²)`, with the Leibniz derivative
combining the radial derivative of `phi` and the derivative `2z · complexCoordinateCLM` of `z²`. -/
theorem degreeTwoFactor_hasFDerivAt {phi : ℝ → ℂ} {phi' : ℂ}
    {y : WholePlane} (hphi : HasDerivAt phi phi' (squaredRadius y)) :
    HasFDerivAt (degreeTwoFactor phi)
      ((complexCoordinate y ^ 2) •
          ((2 • innerSL ℝ y).smulRight phi') +
        (radialScalar phi y) •
          ((2 • complexCoordinate y ^ (2 - 1)) • complexCoordinateCLM)) y := by
  have hz2 := (complexCoordinate_hasFDerivAt y).pow 2
  have h := hz2.mul (radialScalar_hasFDerivAt hphi)
  apply h.congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall fun x ↦ rfl

/-! ## Explicit first derivatives -/

/-- `complexCoordinateCLM` sends the first standard basis vector of the plane to `1`. -/
theorem complexCoordinateCLM_basis_zero :
    complexCoordinateCLM (wholePlaneBasis (0 : Fin 2)) = 1 := by
  simp [complexCoordinateCLM, wholePlaneBasis]

/-- `complexCoordinateCLM` sends the second standard basis vector of the plane to `i`. -/
theorem complexCoordinateCLM_basis_one :
    complexCoordinateCLM (wholePlaneBasis (1 : Fin 2)) = Complex.I := by
  simp [complexCoordinateCLM, wholePlaneBasis]

/-- The squared radius vanishes at the origin. -/
@[simp] theorem squaredRadius_zero : squaredRadius (0 : WholePlane) = 0 := by
  simp [squaredRadius]

/-- The complex coordinate vanishes at the origin. -/
@[simp] theorem complexCoordinate_zero : complexCoordinate (0 : WholePlane) = 0 := by
  simp [complexCoordinate]

/-- At the origin a squared-radius profile takes the value `phi 0`. -/
@[simp] theorem radialScalar_zero (phi : ℝ → ℂ) :
    radialScalar phi (0 : WholePlane) = phi 0 := by
  simp [radialScalar]

/-- The degree-two factor `z² phi(‖y‖²)` vanishes at the origin, since `z` does. -/
@[simp] theorem degreeTwoFactor_zero (phi : ℝ → ℂ) :
    degreeTwoFactor phi (0 : WholePlane) = 0 := by
  simp [degreeTwoFactor]

/-- A `Cⁿ` scalar profile of the squared radius is `Cⁿ` on the plane: smoothness of the radial
profile transfers through the smooth substitution `‖y‖²`, with no loss at the origin. -/
theorem radialScalar_contDiff {n : WithTop ℕ∞} {phi : ℝ → ℂ}
    (hphi : ContDiff ℝ n phi) :
    ContDiff ℝ n (radialScalar phi) := by
  have hs : ContDiff ℝ n squaredRadius :=
    squaredRadius_contDiff.of_le (by simp)
  exact hphi.comp hs

/-- If the radial profile `phi` is `Cⁿ`, the degree-two factor `z² phi(‖y‖²)` is `Cⁿ` on the whole
plane, the origin included. -/
theorem degreeTwoFactor_contDiff {n : WithTop ℕ∞} {phi : ℝ → ℂ}
    (hphi : ContDiff ℝ n phi) :
    ContDiff ℝ n (degreeTwoFactor phi) := by
  unfold degreeTwoFactor
  have hz : ContDiff ℝ n complexCoordinate :=
    complexCoordinate_contDiff.of_le (by simp)
  exact (hz.pow 2).mul (radialScalar_contDiff hphi)

end CartesianRadialRegularity
end FastDynamo

/-!
## The real squared-radius profiles of the interior branches

The scalar interior branches have the exact axis factorizations

`B_minus(r) = Phi_minus(r^2)` and `B_plus(r) = r^2 Phi_plus(r^2)`.

The coefficient functions are entire in the squared-radius variable, so their real
restrictions `minusOriginProfile`, `plusOriginProfile` are smooth; their values at the origin
are recorded.  No exterior, interface, Sobolev, or eigenmode claim is made.
-/

noncomputable section

namespace FastDynamo
namespace PonomarenkoOriginProfiles

open Complex
open PonomarenkoOriginCoefficients
open ModifiedBesselBoundaryBehavior
open CartesianRadialRegularity

/-! ## The two real squared-radius profiles -/

/-- The signed order-zero coefficient restricted to the real squared-radius variable. -/
def minusOriginProfile (kappa : ℂ) (s : ℝ) : ℂ :=
  minusInsideSquaredRadiusCoefficient kappa (s : ℂ)

/-- The order-two coefficient restricted to the real squared-radius variable. -/
def plusOriginProfile (kappa : ℂ) (s : ℝ) : ℂ :=
  plusInsideSquaredRadiusCoefficient kappa (s : ℂ)

/-- The order-zero squared-radius profile `Φ₋` is smooth on `ℝ`, being the restriction of an entire
function of the squared-radius variable. -/
theorem minusOriginProfile_contDiff (kappa : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (minusOriginProfile kappa) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun s : ℝ ↦ minusInsideSquaredRadiusCoefficient kappa (s : ℂ))
  exact (minusInsideSquaredRadiusCoefficient_real_contDiff kappa).of_le (by simp)

/-- The order-two squared-radius profile `Φ₊` is smooth on `ℝ`. -/
theorem plusOriginProfile_contDiff (kappa : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (plusOriginProfile kappa) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun s : ℝ ↦ plusInsideSquaredRadiusCoefficient kappa (s : ℂ))
  exact (plusInsideSquaredRadiusCoefficient_real_contDiff kappa).of_le (by simp)

/-- Value of the order-zero squared-radius profile on the polar axis: `Φ₋(0) = -K₀(κ)`, which is
`B₋(0)` since `I₀(0) = 1`. -/
@[simp] theorem minusOriginProfile_zero (kappa : ℂ) :
    minusOriginProfile kappa 0 = -ModifiedBessel.K0 kappa := by
  simp [minusOriginProfile]

/-- Value of the order-two squared-radius profile on the polar axis: `Φ₊(0) = K₂(κ) κ²/8`, the
leading power-series coefficient of `I₂`. -/
@[simp] theorem plusOriginProfile_zero (kappa : ℂ) :
    plusOriginProfile kappa 0 = ModifiedBessel.K2 kappa * (kappa ^ 2 / 8) := by
  simp [plusOriginProfile]

end PonomarenkoOriginProfiles
end FastDynamo

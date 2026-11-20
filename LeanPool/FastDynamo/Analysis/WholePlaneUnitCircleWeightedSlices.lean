/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneUnitCircleSlices
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Weighted coordinate charts on the whole-plane unit circle

The normal component in a coordinate direction cancels the Jacobian of the
corresponding two-sheeted graph chart.  Concretely, if the coordinate selected
by `j` is the inner slice variable and `x` is the transverse variable, then

`integral (y j) J(y) d sigma(y) = integral (J(x,+sqrt(1-x^2)) -
  J(x,-sqrt(1-x^2))) dx`.

This file separates the elementary angular change of variables from the
measure-identification step.  The former is useful on its own and is stated for
an arbitrary complete real normed target.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Real Set Module
open scoped Interval Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section SphereMeasureNaturality

variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

/-- A real linear isometry equivalence restricts to a homeomorphism of unit
spheres. -/
def linearIsometryUnitSphereHomeomorph (e : F ≃ₗᵢ[ℝ] G) :
    Metric.sphere (0 : F) 1 ≃ₜ Metric.sphere (0 : G) 1 where
  toFun x := ⟨e x, by
    simp⟩
  invFun y := ⟨e.symm y, by
    simp⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] in
/-- The induced homeomorphism of unit spheres acts by the underlying isometry: the ambient value
of the image point is `e x`. -/
@[simp] theorem linearIsometryUnitSphereHomeomorph_coe
    (e : F ≃ₗᵢ[ℝ] G) (x : Metric.sphere (0 : F) 1) :
    ((linearIsometryUnitSphereHomeomorph e x : Metric.sphere (0 : G) 1) : G) = e x :=
  rfl

/-- Naturality of Mathlib's canonical sphere measure under a volume-preserving
linear isometry equivalence.  The proof unfolds `Measure.toSphere_apply'`; the
only set calculation is that a linear map commutes with positive radial
scaling. -/
theorem measurePreserving_linearIsometryUnitSphereHomeomorph
    (e : F ≃ₗᵢ[ℝ] G)
    (he : MeasurePreserving e (volume : Measure F) (volume : Measure G)) :
    MeasurePreserving (linearIsometryUnitSphereHomeomorph e)
      (volume : Measure F).toSphere (volume : Measure G).toSphere := by
  refine ⟨(linearIsometryUnitSphereHomeomorph e).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Set.measure_eq_iInf_isOpen, Set.measure_eq_iInf_isOpen]
  congr! 4 with U _ hU
  rw [(linearIsometryUnitSphereHomeomorph e).measurableEmbedding.map_apply
      (volume : Measure F).toSphere U,
    Measure.toSphere_apply' _ (hU.preimage
      (linearIsometryUnitSphereHomeomorph e).continuous).measurableSet,
    Measure.toSphere_apply' _ hU.measurableSet]
  have hcone :
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 •
          ((fun y : Metric.sphere (0 : G) 1 ↦ (y : G)) '' U)) =
        Set.Ioo (0 : ℝ) 1 •
          ((fun x : Metric.sphere (0 : F) 1 ↦ (x : F)) ''
            ((linearIsometryUnitSphereHomeomorph e) ⁻¹' U)) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨r, hr, _, ⟨y, hy, rfl⟩, hry⟩
      let x : Metric.sphere (0 : F) 1 :=
        (linearIsometryUnitSphereHomeomorph e).symm y
      refine ⟨r, hr, (x : F), ⟨x, ?_, rfl⟩, ?_⟩
      · simpa [x] using hy
      · apply e.injective
        rw [map_smul]
        dsimp [x, linearIsometryUnitSphereHomeomorph]
        simpa using hry
    · rintro ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨r, hr, (linearIsometryUnitSphereHomeomorph e x : G),
        ⟨linearIsometryUnitSphereHomeomorph e x, hx, rfl⟩, ?_⟩
      simp
  have hmeasCone : MeasurableSet
      (Set.Ioo (0 : ℝ) 1 •
        ((fun y : Metric.sphere (0 : G) 1 ↦ (y : G)) '' U)) :=
    (isOpen_Ioo.smul_sphere one_ne_zero (by simp) hU).measurableSet
  rw [e.toLinearEquiv.finrank_eq, ← hcone,
    he.measure_preimage hmeasCone.nullMeasurableSet]

end SphereMeasureNaturality

section ComplexAngularMeasure

/-- Positivity of `2π`, needed to form `AddCircle (2π)` and its Haar measure. -/
local instance twoPiPositiveFact : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- Mathlib's `Circle` is given its Borel σ-algebra. -/
noncomputable instance complexCircleMeasurableSpace : MeasurableSpace Circle :=
  borel Circle

/-- With that σ-algebra `Circle` is a Borel space, so measures on it are determined by their
values on open sets. -/
instance complexCircleBorelSpace : BorelSpace Circle :=
  ⟨rfl⟩

/-- The definitional complex unit-sphere carrier and `Circle` have the same
topology; `Circle` is its own named type. -/
def circleMetricSphereHomeomorph :
    Circle ≃ₜ Metric.sphere (0 : ℂ) 1 where
  toFun z := ⟨(z : ℂ), by
    exact mem_sphere_zero_iff_norm.2 (Circle.norm_coe z)⟩
  invFun z := ⟨(z : ℂ), by
    simp [Submonoid.unitSphere]⟩
  left_inv z := by ext; rfl
  right_inv z := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The homeomorphism from `Circle` onto the metric unit sphere of `ℂ` is the identity on the
underlying complex numbers. -/
@[simp] theorem circleMetricSphereHomeomorph_coe (z : Circle) :
    ((circleMetricSphereHomeomorph z : Metric.sphere (0 : ℂ) 1) : ℂ) = z :=
  rfl

/-- Its inverse is likewise the identity on the underlying complex numbers. -/
@[simp] theorem circleMetricSphereHomeomorph_symm_coe
    (z : Metric.sphere (0 : ℂ) 1) :
    ((circleMetricSphereHomeomorph.symm z : Circle) : ℂ) = z :=
  rfl

/-- Multiplication by a unit complex number, viewed as a real linear
isometry equivalence. -/
def complexUnitRotation (a : Circle) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  { DistribMulAction.toLinearEquiv ℝ ℂ a with
    norm_map' := fun z ↦ by
      change ‖(a : ℂ) * z‖ = ‖z‖
      rw [norm_mul, Circle.norm_coe, one_mul] }

/-- The rotation isometry attached to a unit complex number `a` acts by multiplication by `a`. -/
@[simp] theorem complexUnitRotation_apply (a : Circle) (z : ℂ) :
    complexUnitRotation a z = (a : ℂ) * z :=
  rfl

/-- Mathlib's polar-coordinate sphere measure, regarded as a measure on the
complex unit circle. -/
def complexUnitCircleSphereMeasure : Measure Circle :=
  Measure.map circleMetricSphereHomeomorph.symm
    (volume : Measure ℂ).toSphere

/-- The polar-coordinate sphere measure on `Circle` is invariant under left multiplication by
any unit complex number, because that multiplication is a volume-preserving linear isometry
of `ℂ`. -/
theorem map_mul_left_complexUnitCircleSphereMeasure (a : Circle) :
    Measure.map (fun z : Circle ↦ a * z) complexUnitCircleSphereMeasure =
      complexUnitCircleSphereMeasure := by
  have h := measurePreserving_linearIsometryUnitSphereHomeomorph
    (complexUnitRotation a) (complexUnitRotation a).measurePreserving
  let R := linearIsometryUnitSphereHomeomorph (complexUnitRotation a)
  have hintertwine :
      (fun z : Circle ↦ a * z) ∘ circleMetricSphereHomeomorph.symm =
        circleMetricSphereHomeomorph.symm ∘ R := by
    funext z
    apply Circle.ext
    rfl
  calc
    Measure.map (fun z : Circle ↦ a * z) complexUnitCircleSphereMeasure =
        Measure.map ((fun z : Circle ↦ a * z) ∘
          circleMetricSphereHomeomorph.symm) (volume : Measure ℂ).toSphere := by
      rw [complexUnitCircleSphereMeasure,
        Measure.map_map (continuous_const_mul a).measurable
          circleMetricSphereHomeomorph.symm.measurable]
    _ = Measure.map (circleMetricSphereHomeomorph.symm ∘ R)
          (volume : Measure ℂ).toSphere := by rw [hintertwine]
    _ = Measure.map circleMetricSphereHomeomorph.symm
          (Measure.map R (volume : Measure ℂ).toSphere) := by
      rw [Measure.map_map circleMetricSphereHomeomorph.symm.measurable
        R.measurable]
    _ = complexUnitCircleSphereMeasure := by
      rw [h.map_eq]
      rfl

/-- Instance form of the left invariance of the polar-coordinate sphere measure on `Circle`. -/
instance complexUnitCircleSphereMeasure_isMulLeftInvariant :
    Measure.IsMulLeftInvariant complexUnitCircleSphereMeasure where
  map_mul_left_eq_self := map_mul_left_complexUnitCircleSphereMeasure

/-- The polar-coordinate sphere measure on `Circle` is finite, being the pushforward of a finite
measure. -/
instance complexUnitCircleSphereMeasure_isFiniteMeasure :
    IsFiniteMeasure complexUnitCircleSphereMeasure := by
  unfold complexUnitCircleSphereMeasure
  infer_instance

/-- The polar-coordinate sphere measure is a Haar measure on the compact group `Circle`: it is
left invariant, finite on compacts, and positive on nonempty open sets. -/
instance complexUnitCircleSphereMeasure_isHaarMeasure :
    Measure.IsHaarMeasure complexUnitCircleSphereMeasure where
  lt_top_of_isCompact K _ := measure_lt_top _ K
  open_pos U hU hUne := by
    simpa [complexUnitCircleSphereMeasure] using
      (circleMetricSphereHomeomorph.symm.continuous.isOpenPosMeasure_map
        circleMetricSphereHomeomorph.symm.surjective).open_pos U hU hUne

/-- Lebesgue measure on one angular period, transported to `Circle`. -/
def complexUnitCircleAngularMeasure : Measure Circle :=
  Measure.map AddCircle.homeomorphCircle'
    (volume : Measure (AddCircle (2 * Real.pi)))

/-- Angular Lebesgue measure transported to `Circle` is invariant under left multiplication:
under the identification with `AddCircle (2π)`, rotation becomes translation. -/
theorem map_mul_left_complexUnitCircleAngularMeasure (a : Circle) :
    Measure.map (fun z : Circle ↦ a * z) complexUnitCircleAngularMeasure =
      complexUnitCircleAngularMeasure := by
  let b : AddCircle (2 * Real.pi) := AddCircle.homeomorphCircle'.symm a
  have hintertwine :
      (fun z : Circle ↦ a * z) ∘ AddCircle.homeomorphCircle' =
        AddCircle.homeomorphCircle' ∘ (fun z ↦ b + z) := by
    funext z
    dsimp only [Function.comp_apply]
    rw [← AddCircle.homeomorphCircle'.apply_symm_apply a]
    have hhomeo (w : AddCircle (2 * Real.pi)) :
        AddCircle.homeomorphCircle' w = AddCircle.toCircle w := by
      induction w using QuotientAddGroup.induction_on
      rw [AddCircle.homeomorphCircle'_apply_mk,
        AddCircle.toCircle_apply_mk]
      congr 1
      field_simp [Real.pi_ne_zero]
    rw [hhomeo, hhomeo, hhomeo]
    simpa [b] using (AddCircle.toCircle_add b z).symm
  calc
    Measure.map (fun z : Circle ↦ a * z) complexUnitCircleAngularMeasure =
        Measure.map ((fun z : Circle ↦ a * z) ∘
          AddCircle.homeomorphCircle')
          (volume : Measure (AddCircle (2 * Real.pi))) := by
      rw [complexUnitCircleAngularMeasure,
        Measure.map_map (continuous_const_mul a).measurable
          AddCircle.homeomorphCircle'.measurable]
    _ = Measure.map (AddCircle.homeomorphCircle' ∘ (fun z ↦ b + z))
          (volume : Measure (AddCircle (2 * Real.pi))) := by rw [hintertwine]
    _ = Measure.map AddCircle.homeomorphCircle'
          (Measure.map (fun z ↦ b + z)
            (volume : Measure (AddCircle (2 * Real.pi)))) := by
      rw [Measure.map_map AddCircle.homeomorphCircle'.measurable
        (continuous_const_add b).measurable]
    _ = complexUnitCircleAngularMeasure := by
      rw [MeasureTheory.map_add_left_eq_self]
      rfl

/-- Instance form of the left invariance of the transported angular Lebesgue measure. -/
instance complexUnitCircleAngularMeasure_isMulLeftInvariant :
    Measure.IsMulLeftInvariant complexUnitCircleAngularMeasure where
  map_mul_left_eq_self := map_mul_left_complexUnitCircleAngularMeasure

/-- The transported angular measure is finite, one period of Lebesgue measure having finite
mass. -/
instance complexUnitCircleAngularMeasure_isFiniteMeasure :
    IsFiniteMeasure complexUnitCircleAngularMeasure := by
  unfold complexUnitCircleAngularMeasure
  infer_instance

/-- The transported angular measure is a Haar measure on `Circle`: left invariant, finite on
compacts, and positive on nonempty open sets. -/
instance complexUnitCircleAngularMeasure_isHaarMeasure :
    Measure.IsHaarMeasure complexUnitCircleAngularMeasure where
  lt_top_of_isCompact K _ := measure_lt_top _ K
  open_pos U hU hUne := by
    simpa [complexUnitCircleAngularMeasure] using
      (AddCircle.homeomorphCircle'.continuous.isOpenPosMeasure_map
        AddCircle.homeomorphCircle'.surjective).open_pos U hU hUne

/-- The total angular mass of `Circle` is `2π`. -/
@[simp] theorem complexUnitCircleAngularMeasure_univ :
    complexUnitCircleAngularMeasure Set.univ =
      ENNReal.ofReal (2 * Real.pi) := by
  rw [complexUnitCircleAngularMeasure,
    Measure.map_apply AddCircle.homeomorphCircle'.measurable MeasurableSet.univ]
  simp

/-- For an additive Haar measure on a finite-dimensional real normed space and any `p > 0`, the
measure of the unit ball equals `(∫ exp(-‖x‖^p)) / Γ(dim/p + 1)`; the proof is the radial
decomposition of the integral. -/
private theorem measure_unitBall_eq_integral_div_gamma_aux
    {F : Type*} {p : ℝ}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (mu : Measure F) [Measure.IsAddHaarMeasure mu] (hp : 0 < p) :
    mu (Metric.ball 0 1) =
      ENNReal.ofReal
        ((∫ x : F, Real.exp (-‖x‖ ^ p) ∂mu) /
          Real.Gamma (finrank ℝ F / p + 1)) := by
  obtain hF | hF := subsingleton_or_nontrivial F
  · rw [(Metric.nonempty_ball.mpr zero_lt_one).eq_zero, ← setIntegral_univ,
      Set.univ_nonempty.eq_zero, integral_singleton, finrank_zero_of_subsingleton,
      Nat.cast_zero, zero_div, zero_add, Real.Gamma_one, div_one, norm_zero,
      Real.zero_rpow hp.ne', neg_zero, Real.exp_zero, smul_eq_mul, mul_one,
      measureReal_def, ENNReal.ofReal_toReal (measure_ne_top mu {0})]
  · have hdim : (0 : ℝ) < finrank ℝ F := Nat.cast_pos.mpr finrank_pos
    have hradial :
        ((∫ y in Set.Ioi (0 : ℝ),
              y ^ (finrank ℝ F - 1) • Real.exp (-y ^ p)) /
            Real.Gamma ((finrank ℝ F) / p + 1)) *
          (finrank ℝ F) = 1 := by
      simp_rw [← Real.rpow_natCast _ (finrank ℝ F - 1), smul_eq_mul,
        Nat.cast_sub finrank_pos, Nat.cast_one]
      rw [integral_rpow_mul_exp_neg_rpow hp (by linarith), sub_add_cancel,
        Real.Gamma_add_one (ne_of_gt (by positivity))]
      field
    rw [MeasureTheory.integral_fun_norm_addHaar mu
        (fun x => Real.exp (-x ^ p)),
      nsmul_eq_mul, smul_eq_mul, mul_div_assoc, mul_div_assoc, mul_comm,
      mul_assoc, hradial, mul_one, MeasureTheory.ofReal_measureReal _]
    exact ne_of_lt measure_ball_lt_top

/-- The Lebesgue measure of the unit ball of `ℂ` is `π`, obtained from the previous formula with
`p = 2` and the Gaussian integral. -/
private theorem complex_volume_unitBall :
    (volume : Measure ℂ) (Metric.ball 0 1) = ENNReal.ofReal Real.pi := by
  rw [measure_unitBall_eq_integral_div_gamma_aux (volume : Measure ℂ)
    (show (0 : ℝ) < 2 by positivity)]
  have hfactor :
      (fun p : ℝ × ℝ ↦
          Real.exp (-‖Complex.measurableEquivRealProd.symm p‖ ^ (2 : ℝ))) =
        fun p : ℝ × ℝ ↦
          Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2) := by
    funext p
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast,
      Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.measurableEquivRealProd_symm_apply]
    rw [← Real.exp_add]
    congr 1
    ring
  have hgauss :
      (∫ z : ℂ, Real.exp (-‖z‖ ^ (2 : ℝ))) = Real.pi := by
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
      Complex.measurableEquivRealProd.symm.measurableEmbedding,
      hfactor, Measure.volume_eq_prod]
    calc
      (∫ p : ℝ × ℝ,
          Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2)
            ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) =
          (∫ x : ℝ, Real.exp (-x ^ 2)) *
            ∫ y : ℝ, Real.exp (-y ^ 2) :=
        MeasureTheory.integral_prod_mul
          (fun x : ℝ ↦ Real.exp (-x ^ 2))
          (fun y : ℝ ↦ Real.exp (-y ^ 2))
      _ = Real.pi := by
        have hg : (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
          simpa using integral_gaussian (1 : ℝ)
        rw [hg]
        nlinarith [Real.sq_sqrt Real.pi_nonneg]
  rw [hgauss, Complex.finrank_real_complex]
  norm_num [Real.Gamma_nat_eq_factorial]

/-- The total polar-coordinate sphere mass of `Circle` is `2π`, twice the area `π` of the unit
disk; this fixes the normalization of the sphere measure. -/
@[simp] theorem complexUnitCircleSphereMeasure_univ :
    complexUnitCircleSphereMeasure Set.univ =
      ENNReal.ofReal (2 * Real.pi) := by
  rw [complexUnitCircleSphereMeasure,
    Measure.map_apply circleMetricSphereHomeomorph.symm.measurable
      MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [Measure.toSphere_apply_univ, Complex.finrank_real_complex,
    complex_volume_unitBall]
  norm_num [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ))]

/-- The polar-coordinate sphere measure is exactly (not merely a scalar
multiple of) angular Lebesgue measure. -/
theorem complexUnitCircleSphereMeasure_eq_angularMeasure :
    complexUnitCircleSphereMeasure = complexUnitCircleAngularMeasure := by
  have hscale := MeasureTheory.Measure.isMulInvariant_eq_smul_of_compactSpace
    complexUnitCircleSphereMeasure complexUnitCircleAngularMeasure
  have huniv := congrArg (fun mu : Measure Circle ↦ mu Set.univ) hscale
  simp only [complexUnitCircleSphereMeasure_univ,
    complexUnitCircleAngularMeasure_univ, Measure.smul_apply] at huniv
  have hp0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by positivity
  have hptop : ENNReal.ofReal (2 * Real.pi) ≠ ⊤ := by finiteness
  have hc_coe :
      (↑(MeasureTheory.Measure.haarScalarFactor
        complexUnitCircleSphereMeasure complexUnitCircleAngularMeasure) : ENNReal) = 1 :=
    (ENNReal.mul_eq_right hp0 hptop).mp huniv.symm
  have hc : MeasureTheory.Measure.haarScalarFactor complexUnitCircleSphereMeasure
      complexUnitCircleAngularMeasure = 1 := by
    exact ENNReal.coe_eq_one.mp hc_coe
  simpa [hc] using hscale

/-- Integration against the canonical complex unit-sphere measure is
integration over one ordinary angular period. -/
theorem integral_complexUnitCircleSphereMeasure_eq_intervalIntegral
    (f : Circle → E) :
    (∫ z : Circle, f z ∂complexUnitCircleSphereMeasure) =
      ∫ theta in (0 : ℝ)..2 * Real.pi, f (Circle.exp theta) := by
  calc
    (∫ z : Circle, f z ∂complexUnitCircleSphereMeasure) =
        ∫ z : Circle, f z ∂complexUnitCircleAngularMeasure := by
      rw [complexUnitCircleSphereMeasure_eq_angularMeasure]
    _ = ∫ z : AddCircle (2 * Real.pi),
          f (AddCircle.homeomorphCircle' z) := by
      exact MeasureTheory.integral_map_equiv
        AddCircle.homeomorphCircle'.toMeasurableEquiv f
    _ = ∫ theta in (0 : ℝ)..2 * Real.pi,
          f (Circle.exp theta) := by
      rw [← AddCircle.intervalIntegral_preimage
        (2 * Real.pi) 0 (fun z : AddCircle (2 * Real.pi) ↦
          f (AddCircle.homeomorphCircle' z))]
      simp only [zero_add]
      apply intervalIntegral.integral_congr
      intro theta _
      change f (AddCircle.homeomorphCircle' (theta : AddCircle (2 * Real.pi))) =
        f (Circle.exp theta)
      rw [AddCircle.homeomorphCircle'_apply_mk]

end ComplexAngularMeasure

/-- Ambient upper graph of the unit circle in the coordinate system whose
selected coordinate is `j`.  Values outside `[-1,1]` are harmless because all
uses below integrate over that interval. -/
def wholePlaneUnitCircleUpperPoint (j : Fin 2) (x : ℝ) : WholePlane :=
  wholePlaneSliceEquiv j (x, Real.sqrt (1 - x ^ 2))

/-- Ambient lower graph of the unit circle in the coordinate system whose
selected coordinate is `j`. -/
def wholePlaneUnitCircleLowerPoint (j : Fin 2) (x : ℝ) : WholePlane :=
  wholePlaneSliceEquiv j (x, -(Real.sqrt (1 - x ^ 2)))

/-- The angular parametrisation adapted to coordinate direction `j`: its
selected coordinate is `sin theta` and its transverse coordinate is
`cos theta`. -/
def wholePlaneUnitCircleAnglePoint (j : Fin 2) (theta : ℝ) : WholePlane :=
  wholePlaneSliceEquiv j (Real.cos theta, Real.sin theta)

/-- The selected coordinate of the angular parametrization adapted to direction `j` is
`sin θ`. -/
@[simp] theorem wholePlaneUnitCircleAnglePoint_apply_selected
    (j : Fin 2) (theta : ℝ) :
    wholePlaneUnitCircleAnglePoint j theta j = Real.sin theta := by
  simp [wholePlaneUnitCircleAnglePoint]

/-- The angular parametrization lands on the unit circle: its Euclidean norm is one. -/
theorem norm_wholePlaneUnitCircleAnglePoint
    (j : Fin 2) (theta : ℝ) :
    ‖wholePlaneUnitCircleAnglePoint j theta‖ = 1 := by
  have hsq :
      ‖wholePlaneUnitCircleAnglePoint j theta‖ ^ 2 = 1 := by
    rw [wholePlaneUnitCircleAnglePoint, norm_sq_wholePlaneSliceEquiv]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  nlinarith [norm_nonneg (wholePlaneUnitCircleAnglePoint j theta)]

/-- The angular point, bundled as an element of the unit circle. -/
def wholePlaneUnitCircleAngle (j : Fin 2) (theta : ℝ) :
    WholePlaneUnitCircle :=
  ⟨wholePlaneUnitCircleAnglePoint j theta, by
    simpa [mem_sphere_zero_iff_norm] using
      norm_wholePlaneUnitCircleAnglePoint j theta⟩

/-- The bundled circle point at angle `θ` has the angular parametrization as its ambient
value. -/
@[simp] theorem wholePlaneUnitCircleAngle_coe
    (j : Fin 2) (theta : ℝ) :
    (wholePlaneUnitCircleAngle j theta : WholePlane) =
      wholePlaneUnitCircleAnglePoint j theta :=
  rfl

/-- The coordinate-adapted isometry from the whole plane to `ℂ`.  In slice
coordinates it always sends `(x,t)` to `x + t I`, for both coordinate
directions. -/
def wholePlaneSliceComplexEquiv (j : Fin 2) : WholePlane ≃ₗᵢ[ℝ] ℂ :=
  if j = 0 then
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.swap (0 : Fin 2) 1)).trans
        Complex.orthonormalBasisOneI.repr.symm
  else
    Complex.orthonormalBasisOneI.repr.symm

/-- In slice coordinates the coordinate-adapted isometry to `ℂ` sends `(x, t)` to `x + it`, for
both choices of the selected coordinate direction. -/
@[simp] theorem wholePlaneSliceComplexEquiv_apply_slice
    (j : Fin 2) (x t : ℝ) :
    wholePlaneSliceComplexEquiv j (wholePlaneSliceEquiv j (x, t)) =
      x + t * Complex.I := by
  fin_cases j <;>
    simp [wholePlaneSliceComplexEquiv,
      LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply]

/-- The unit-circle homeomorphism induced by the coordinate-adapted isometry
to `ℂ`. -/
def wholePlaneUnitCircleCircleHomeomorph (j : Fin 2) :
    WholePlaneUnitCircle ≃ₜ Circle :=
  (linearIsometryUnitSphereHomeomorph
    (wholePlaneSliceComplexEquiv j)).trans circleMetricSphereHomeomorph.symm

/-- The coordinate-adapted circle homeomorphism carries the angular point at `θ` to
`exp(iθ) ∈ Circle`, so the two angular parametrizations agree. -/
@[simp] theorem wholePlaneUnitCircleCircleHomeomorph_apply_angle
    (j : Fin 2) (theta : ℝ) :
    wholePlaneUnitCircleCircleHomeomorph j
      (wholePlaneUnitCircleAngle j theta) = Circle.exp theta := by
  apply Circle.ext
  change wholePlaneSliceComplexEquiv j
      (wholePlaneUnitCircleAnglePoint j theta) = (Circle.exp theta : ℂ)
  rw [wholePlaneUnitCircleAnglePoint,
    wholePlaneSliceComplexEquiv_apply_slice]
  simp [Circle.coe_exp, Complex.exp_mul_I]

/-- The coordinate-adapted circle homeomorphism preserves the canonical
sphere measure. -/
theorem measurePreserving_wholePlaneUnitCircleCircleHomeomorph (j : Fin 2) :
    MeasurePreserving (wholePlaneUnitCircleCircleHomeomorph j)
      wholePlaneUnitCircleMeasure complexUnitCircleSphereMeasure := by
  have hSphere : MeasurePreserving
      (linearIsometryUnitSphereHomeomorph (wholePlaneSliceComplexEquiv j))
      (volume : Measure WholePlane).toSphere (volume : Measure ℂ).toSphere :=
    measurePreserving_linearIsometryUnitSphereHomeomorph
      (wholePlaneSliceComplexEquiv j)
      (wholePlaneSliceComplexEquiv j).measurePreserving
  have hCircle : MeasurePreserving circleMetricSphereHomeomorph.symm
      (volume : Measure ℂ).toSphere complexUnitCircleSphereMeasure := by
    refine ⟨circleMetricSphereHomeomorph.symm.measurable, ?_⟩
    rfl
  refine ⟨(wholePlaneUnitCircleCircleHomeomorph j).measurable, ?_⟩
  change Measure.map
      (circleMetricSphereHomeomorph.symm ∘
        linearIsometryUnitSphereHomeomorph (wholePlaneSliceComplexEquiv j))
      (volume : Measure WholePlane).toSphere = complexUnitCircleSphereMeasure
  rw [← Measure.map_map circleMetricSphereHomeomorph.symm.measurable
    (linearIsometryUnitSphereHomeomorph
      (wholePlaneSliceComplexEquiv j)).measurable,
    hSphere.map_eq, hCircle.map_eq]

/-- The canonical whole-plane unit-circle measure is ordinary angular
Lebesgue measure under every coordinate-adapted angular parametrisation. -/
theorem integral_wholePlaneUnitCircle_eq_intervalIntegral
    (j : Fin 2) (f : WholePlaneUnitCircle → E) :
    (∫ y : WholePlaneUnitCircle, f y ∂wholePlaneUnitCircleMeasure) =
      ∫ theta in (0 : ℝ)..2 * Real.pi,
        f (wholePlaneUnitCircleAngle j theta) := by
  let P := wholePlaneUnitCircleCircleHomeomorph j
  have hP := measurePreserving_wholePlaneUnitCircleCircleHomeomorph j
  calc
    (∫ y : WholePlaneUnitCircle, f y ∂wholePlaneUnitCircleMeasure) =
        ∫ z : Circle, f (P.symm z) ∂complexUnitCircleSphereMeasure := by
      have h := hP.integral_comp P.measurableEmbedding
        (fun z : Circle ↦ f (P.symm z))
      simpa [P] using h
    _ = ∫ theta in (0 : ℝ)..2 * Real.pi,
          f (P.symm (Circle.exp theta)) :=
      integral_complexUnitCircleSphereMeasure_eq_intervalIntegral
        (fun z : Circle ↦ f (P.symm z))
    _ = ∫ theta in (0 : ℝ)..2 * Real.pi,
          f (wholePlaneUnitCircleAngle j theta) := by
      apply intervalIntegral.integral_congr
      intro theta _
      change f (P.symm (Circle.exp theta)) =
        f (wholePlaneUnitCircleAngle j theta)
      rw [← wholePlaneUnitCircleCircleHomeomorph_apply_angle j theta]
      exact congrArg f
        (P.symm_apply_apply (wholePlaneUnitCircleAngle j theta))

/-- On the upper semicircle `0 ≤ θ ≤ π` the angular parametrization is the upper graph evaluated
at the transverse coordinate `x = cos θ`. -/
theorem wholePlaneUnitCircleAnglePoint_eq_upper
    (j : Fin 2) {theta : ℝ} (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi) :
    wholePlaneUnitCircleAnglePoint j theta =
      wholePlaneUnitCircleUpperPoint j (Real.cos theta) := by
  rw [wholePlaneUnitCircleAnglePoint, wholePlaneUnitCircleUpperPoint,
    Real.sin_eq_sqrt_one_sub_cos_sq h0 hpi]

/-- On the lower semicircle `π ≤ θ ≤ 2π` the angular parametrization is the lower graph
evaluated at the transverse coordinate `x = cos θ`. -/
theorem wholePlaneUnitCircleAnglePoint_eq_lower
    (j : Fin 2) {theta : ℝ} (hpi : Real.pi ≤ theta)
    (htwo : theta ≤ 2 * Real.pi) :
    wholePlaneUnitCircleAnglePoint j theta =
      wholePlaneUnitCircleLowerPoint j (Real.cos theta) := by
  have hs : Real.sin theta ≤ 0 := by
    rw [← Real.sin_sub_two_pi theta]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  have hsqrt : Real.sin theta = -Real.sqrt (1 - Real.cos theta ^ 2) := by
    calc
      Real.sin theta = -|Real.sin theta| := by rw [abs_of_nonpos hs]; simp
      _ = -Real.sqrt (1 - Real.cos theta ^ 2) := by
        rw [Real.abs_sin_eq_sqrt_one_sub_cos_sq]
  rw [wholePlaneUnitCircleAnglePoint, wholePlaneUnitCircleLowerPoint, hsqrt]

/-- The upper graph of the unit circle depends continuously on the transverse coordinate. -/
theorem continuous_wholePlaneUnitCircleUpperPoint (j : Fin 2) :
    Continuous (wholePlaneUnitCircleUpperPoint j) := by
  fin_cases j
  · change Continuous (fun x : ℝ ↦
      (!₂[Real.sqrt (1 - x ^ 2), x] : WholePlane))
    fun_prop
  · change Continuous (fun x : ℝ ↦
      (!₂[x, Real.sqrt (1 - x ^ 2)] : WholePlane))
    fun_prop

/-- The lower graph of the unit circle depends continuously on the transverse coordinate. -/
theorem continuous_wholePlaneUnitCircleLowerPoint (j : Fin 2) :
    Continuous (wholePlaneUnitCircleLowerPoint j) := by
  fin_cases j
  · change Continuous (fun x : ℝ ↦
      (!₂[-Real.sqrt (1 - x ^ 2), x] : WholePlane))
    fun_prop
  · change Continuous (fun x : ℝ ↦
      (!₂[x, -Real.sqrt (1 - x ^ 2)] : WholePlane))
    fun_prop

/-- The angular parametrization of the unit circle depends continuously on the angle. -/
theorem continuous_wholePlaneUnitCircleAnglePoint (j : Fin 2) :
    Continuous (wholePlaneUnitCircleAnglePoint j) := by
  fin_cases j
  · change Continuous (fun theta : ℝ ↦
      (!₂[Real.sin theta, Real.cos theta] : WholePlane))
    fun_prop
  · change Continuous (fun theta : ℝ ↦
      (!₂[Real.cos theta, Real.sin theta] : WholePlane))
    fun_prop

/-- Upper-semicircle substitution `x = cos theta`.  The sign and orientation
cancel, leaving a positively oriented integral over `[-1,1]`. -/
theorem intervalIntegral_sin_smul_comp_angle_eq_upper
    (j : Fin 2) (J : WholePlane → E)
    (hJ : Continuous J) :
    (∫ theta in (0 : ℝ)..Real.pi,
        Real.sin theta • J (wholePlaneUnitCircleAnglePoint j theta)) =
      ∫ x in (-1 : ℝ)..1, J (wholePlaneUnitCircleUpperPoint j x) := by
  let g : ℝ → E := fun x ↦ J (wholePlaneUnitCircleUpperPoint j x)
  have hg : Continuous g := hJ.comp (continuous_wholePlaneUnitCircleUpperPoint j)
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (E := E) (a := (0 : ℝ)) (b := Real.pi)
    (f := Real.cos) (f' := fun theta ↦ -Real.sin theta) (g := g)
    (fun theta _ ↦ Real.hasDerivAt_cos theta) (by fun_prop) hg
  have hcongr :
      (∫ theta in (0 : ℝ)..Real.pi,
          (-Real.sin theta) • g (Real.cos theta)) =
        ∫ theta in (0 : ℝ)..Real.pi,
          (-Real.sin theta) •
            J (wholePlaneUnitCircleAnglePoint j theta) := by
    apply intervalIntegral.integral_congr
    intro theta htheta
    have ht : theta ∈ Set.uIcc (0 : ℝ) Real.pi := htheta
    rw [Set.uIcc_of_le Real.pi_pos.le] at ht
    dsimp only [g, Function.comp_apply]
    rw [wholePlaneUnitCircleAnglePoint_eq_upper j ht.1 ht.2]
  have hsub' :
      (∫ theta in (0 : ℝ)..Real.pi,
          (-Real.sin theta) •
            J (wholePlaneUnitCircleAnglePoint j theta)) =
        -∫ x in (-1 : ℝ)..1, J (wholePlaneUnitCircleUpperPoint j x) := by
    calc
      _ = ∫ theta in (0 : ℝ)..Real.pi,
          (-Real.sin theta) • g (Real.cos theta) := hcongr.symm
      _ = ∫ x in (1 : ℝ)..(-1), g x := by
        simpa only [Function.comp_apply, Real.cos_zero, Real.cos_pi] using hsub
      _ = -∫ x in (-1 : ℝ)..1, g x :=
        intervalIntegral.integral_symm (f := g) (-1) 1
      _ = -∫ x in (-1 : ℝ)..1,
          J (wholePlaneUnitCircleUpperPoint j x) := rfl
  have hneg := congrArg Neg.neg hsub'
  simpa only [← intervalIntegral.integral_neg, neg_smul, neg_neg] using hneg

/-- Lower-semicircle substitution `x = cos theta`.  This time the weighted
integral is the negative of the lower-sheet chart integral. -/
theorem intervalIntegral_sin_smul_comp_angle_eq_neg_lower
    (j : Fin 2) (J : WholePlane → E)
    (hJ : Continuous J) :
    (∫ theta in Real.pi..2 * Real.pi,
        Real.sin theta • J (wholePlaneUnitCircleAnglePoint j theta)) =
      -∫ x in (-1 : ℝ)..1, J (wholePlaneUnitCircleLowerPoint j x) := by
  let g : ℝ → E := fun x ↦ J (wholePlaneUnitCircleLowerPoint j x)
  have hg : Continuous g := hJ.comp (continuous_wholePlaneUnitCircleLowerPoint j)
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (E := E) (a := Real.pi) (b := 2 * Real.pi)
    (f := Real.cos) (f' := fun theta ↦ -Real.sin theta) (g := g)
    (fun theta _ ↦ Real.hasDerivAt_cos theta) (by fun_prop) hg
  have hcongr :
      (∫ theta in Real.pi..2 * Real.pi,
          (-Real.sin theta) • g (Real.cos theta)) =
        ∫ theta in Real.pi..2 * Real.pi,
          (-Real.sin theta) •
            J (wholePlaneUnitCircleAnglePoint j theta) := by
    apply intervalIntegral.integral_congr
    intro theta htheta
    have ht : theta ∈ Set.uIcc Real.pi (2 * Real.pi) := htheta
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
    dsimp only [g, Function.comp_apply]
    rw [wholePlaneUnitCircleAnglePoint_eq_lower j ht.1 ht.2]
  have hsub' :
      (∫ theta in Real.pi..2 * Real.pi,
          (-Real.sin theta) •
            J (wholePlaneUnitCircleAnglePoint j theta)) =
        ∫ x in (-1 : ℝ)..1, J (wholePlaneUnitCircleLowerPoint j x) := by
    calc
      _ = ∫ theta in Real.pi..2 * Real.pi,
          (-Real.sin theta) • g (Real.cos theta) := hcongr.symm
      _ = ∫ x in (-1 : ℝ)..1, g x := by
        simpa only [Function.comp_apply, Real.cos_pi, Real.cos_two_pi] using hsub
      _ = ∫ x in (-1 : ℝ)..1,
          J (wholePlaneUnitCircleLowerPoint j x) := rfl
  have hneg := congrArg Neg.neg hsub'
  simpa only [← intervalIntegral.integral_neg, neg_smul, neg_neg] using hneg

/-- Exact weighted two-sheet chart identity for the angular parametrisation.
There is no normalising constant. -/
theorem intervalIntegral_weighted_unitCircleAngle_eq_upper_sub_lower
    (j : Fin 2) (J : WholePlane → E)
    (hJ : Continuous J) :
    (∫ theta in (0 : ℝ)..2 * Real.pi,
        Real.sin theta • J (wholePlaneUnitCircleAnglePoint j theta)) =
      ∫ x in (-1 : ℝ)..1,
        (J (wholePlaneUnitCircleUpperPoint j x) -
          J (wholePlaneUnitCircleLowerPoint j x)) := by
  have hcont : Continuous (fun theta : ℝ ↦
      Real.sin theta • J (wholePlaneUnitCircleAnglePoint j theta)) :=
    (Real.continuous_sin.smul
      (hJ.comp (continuous_wholePlaneUnitCircleAnglePoint j)))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (0 : ℝ) Real.pi)
    (hcont.intervalIntegrable Real.pi (2 * Real.pi)),
    intervalIntegral_sin_smul_comp_angle_eq_upper j J hJ,
    intervalIntegral_sin_smul_comp_angle_eq_neg_lower j J hJ]
  rw [← sub_eq_add_neg, ← intervalIntegral.integral_sub]
  · simpa [Function.comp_def] using
      (hJ.comp (continuous_wholePlaneUnitCircleUpperPoint j)).intervalIntegrable (-1) 1
  · simpa [Function.comp_def] using
      (hJ.comp (continuous_wholePlaneUnitCircleLowerPoint j)).intervalIntegrable (-1) 1

/-- Exact weighted chart identity for Mathlib's canonical whole-plane unit
circle measure.  The selected normal coordinate cancels the graph Jacobian,
so there is no normalising factor. -/
theorem integral_wholePlaneUnitCircle_coordinate_smul_eq_intervalIntegral
    (j : Fin 2) (J : WholePlane → E)
    (hJ : Continuous J) :
    (∫ y : WholePlaneUnitCircle,
        (y.1 j) • J y.1 ∂wholePlaneUnitCircleMeasure) =
      ∫ x in (-1 : ℝ)..1,
        (J (wholePlaneUnitCircleUpperPoint j x) -
          J (wholePlaneUnitCircleLowerPoint j x)) := by
  rw [integral_wholePlaneUnitCircle_eq_intervalIntegral j]
  simpa only [wholePlaneUnitCircleAngle_coe,
    wholePlaneUnitCircleAnglePoint_apply_selected] using
      intervalIntegral_weighted_unitCircleAngle_eq_upper_sub_lower j J hJ

/-- Set-integral form of the weighted chart identity, matching the open
transverse interval used by the two-jump slice constructors. -/
theorem integral_wholePlaneUnitCircle_coordinate_smul_eq_setIntegral
    (j : Fin 2) (J : WholePlane → E)
    (hJ : Continuous J) :
    (∫ y : WholePlaneUnitCircle,
        (y.1 j) • J y.1 ∂wholePlaneUnitCircleMeasure) =
      ∫ x in Set.Ioo (-1 : ℝ) 1,
        (J (wholePlaneUnitCircleUpperPoint j x) -
          J (wholePlaneUnitCircleLowerPoint j x)) := by
  rw [integral_wholePlaneUnitCircle_coordinate_smul_eq_intervalIntegral j J hJ,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  exact MeasureTheory.setIntegral_congr_set
    (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ))
      (a := (-1 : ℝ)) (b := 1)).symm

end

end FastDynamo

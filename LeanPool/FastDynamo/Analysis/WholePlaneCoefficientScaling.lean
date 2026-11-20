/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.Holder
public import LeanPool.FastDynamo.Analysis.WholePlaneH2
public import LeanPool.FastDynamo.Analysis.WholePlaneScaling
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Affine scaling of whole-plane essentially bounded coefficients

The scaling identity `eq:scaling` of the paper (Lemma 5.2, `lem:exact-renormalization`)
conjugates a placed cell operator by an affine change of variables.  Two different
pullbacks occur there: the normalized `L²` rescaling `U_[p,ℓ] f = ℓ⁻¹ P_[p,ℓ] f`, which is
unitary, and the unnormalized coefficient pullback `P_[p,ℓ] a (y) = a ((y - p) / ℓ)`, which acts
on the velocity coefficients.  Keeping them distinct is exactly what makes the transport and
stretching factors cancel.  `WholePlaneScaling` constructs the first pullback on `L²` only;
this module supplies its chain rule on the weak `H²` graph and constructs the second pullback.

The chain rule is obtained distributionally: the inverse-affine pullback is built on Schwartz
test functions, transposed to tempered distributions, and the Jacobian calculation identifies
that transpose with the normalized `L²` rescaling of `WholePlaneScaling`.  This lifts rescaling
to the weak graph definition of `H²`, first derivatives acquiring `ell⁻¹` and second
derivatives and the Laplacian `ell⁻²`; the lift is a continuous linear equivalence and the
exact graph-norm formula is recorded, since the graph norm is not scale invariant.  Coefficient
pullback is then defined on quotient `L∞`; its covariance with Hölder multiplication is in
`WholePlaneCoefficientScalingCoordinateCompatibility`, and its distributional form in
`WholePlaneLInfTempered`.

## Contents

* Affine rescaling on whole-plane weak Sobolev spaces: the Schwartz and tempered pullbacks, the
  Jacobian identification with normalized `L²` rescaling, and the `H²` graph lift with its
  exact norm formula.
* Affine scaling of whole-plane essentially bounded coefficients: the `L∞` spaces, coordinate
  extraction, and the unnormalized `L∞` pullback with its almost-everywhere representative.
-/

@[expose] public section

/-!
## Affine rescaling on whole-plane weak Sobolev spaces

This part supplies the chain rule for the normalized rescaling of
`WholePlaneScaling`, which is constructed there on `L²` only.  It first constructs the
inverse-affine pullback on Schwartz test functions and its transpose on tempered distributions.  The
Jacobian calculation then identifies that transpose with the
normalized `L²` rescaling.

These results lift the rescaling to the weak graph definition of `H²`.  First
derivatives acquire a factor `ell⁻¹`, second derivatives and the Laplacian
acquire `ell⁻²`, and the lift is a continuous linear equivalence.  The exact
graph-norm formula is recorded because the graph norm is not scale invariant.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped LineDeriv SchwartzMap

/-- Scalar dilation by a positive real number as a real continuous linear
equivalence of the transverse plane. -/
def wholePlaneDilationCLE (ell : ℝ) (hell : 0 < ell) :
    WholePlane ≃L[ℝ] WholePlane :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 ell hell.ne')

/-- The bundled dilation equivalence acts by scalar multiplication: `x ↦ ℓ • x`. -/
@[simp] theorem wholePlaneDilationCLE_apply (ell : ℝ) (hell : 0 < ell)
    (x : WholePlane) :
    wholePlaneDilationCLE ell hell x = ell • x := by
  simp [wholePlaneDilationCLE, Units.smul_def]

/-- Translation of a Schwartz function commutes with coordinate
differentiation. -/
theorem lineDeriv_compSubConst (phi : 𝓢(WholePlane, ℂ))
    (a : WholePlane) (j : Fin 2) :
    ∂_{wholePlaneBasis j} (phi.compSubConstCLM ℂ a) =
      (∂_{wholePlaneBasis j} phi).compSubConstCLM ℂ a := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.compSubConstCLM_apply]
  change (fderiv ℝ (fun y : WholePlane => phi (y - a)) x)
      (wholePlaneBasis j) = _
  rw [show (fun y : WholePlane => phi (y - a)) =
    phi ∘ (fun y => y - a) by rfl]
  rw [fderiv_comp x phi.differentiableAt (by fun_prop :
    DifferentiableAt ℝ (fun y : WholePlane => y - a) x)]
  rw [fderiv_sub_const]
  simp

/-- Pullback of a Schwartz test function by the inverse affine map
`x ↦ p + ell • x`. -/
def wholePlaneRescaleTest (p : WholePlane) (ell : ℝ) (hell : 0 < ell) :
    𝓢(WholePlane, ℂ) →L[ℂ] 𝓢(WholePlane, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (wholePlaneDilationCLE ell hell)).comp
      (SchwartzMap.compSubConstCLM ℂ (-p))

/-- Pointwise value of the inverse-affine Schwartz pullback: `φ` is evaluated at `p + ℓ x`, the
inverse of the cell map `y ↦ (y - p)/ℓ`. -/
@[simp] theorem wholePlaneRescaleTest_apply (p : WholePlane) (ell : ℝ)
    (hell : 0 < ell) (phi : 𝓢(WholePlane, ℂ)) (x : WholePlane) :
    wholePlaneRescaleTest p ell hell phi x = phi (p + ell • x) := by
  simp [wholePlaneRescaleTest]
  congr 1
  abel

/-- The derivative chain rule for inverse-affine Schwartz pullback. -/
theorem lineDeriv_wholePlaneRescaleTest (p : WholePlane) (ell : ℝ)
    (hell : 0 < ell) (phi : 𝓢(WholePlane, ℂ)) (j : Fin 2) :
    ∂_{wholePlaneBasis j} (wholePlaneRescaleTest p ell hell phi) =
      (ell : ℂ) • wholePlaneRescaleTest p ell hell
        (∂_{wholePlaneBasis j} phi) := by
  rw [wholePlaneRescaleTest, ContinuousLinearMap.comp_apply,
    SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
  rw [wholePlaneDilationCLE_apply]
  rw [LineDeriv.lineDerivOp_left_smul]
  rw [lineDeriv_compSubConst]
  rfl

/-- Applying the affine map and then its explicit forward inverse recovers
the original point. -/
theorem wholePlaneAffine_forward_left (p : WholePlane) (ell : ℝ)
    (hell : 0 < ell) (y : WholePlane) :
    p + ell • wholePlaneAffine p ell y = y := by
  ext j
  simp only [wholePlaneAffine, PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply]
  simp only [smul_eq_mul]
  field_simp [hell.ne']
  ring

/-- The affine rescaling map is a measurable embedding. -/
theorem measurableEmbedding_wholePlaneAffine (p : WholePlane) (ell : ℝ)
    (hell : 0 < ell) :
    MeasurableEmbedding (wholePlaneAffine p ell) := by
  apply (show Continuous (wholePlaneAffine p ell) by
    unfold wholePlaneAffine
    fun_prop).measurableEmbedding
  intro x y h
  rw [← wholePlaneAffine_forward_left p ell hell x,
    ← wholePlaneAffine_forward_left p ell hell y, h]

section Distribution

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Normalized affine pullback on tempered distributions, defined by duality
against the inverse-affine pullback of Schwartz tests. -/
def wholePlaneRescaleTempered (p : WholePlane) (ell : ℝ) (hell : 0 < ell) :
    𝓢'(WholePlane, F) →L[ℂ] 𝓢'(WholePlane, F) :=
  (ell : ℂ) • PointwiseConvergenceCLM.precomp F
    (wholePlaneRescaleTest p ell hell)

/-- Duality formula for the normalized affine pullback on tempered distributions: it pairs the
distribution with the inverse-affine pullback of the test function and multiplies by the
normalizing factor `ℓ`. -/
@[simp] theorem wholePlaneRescaleTempered_apply_apply
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (T : 𝓢'(WholePlane, F)) (phi : 𝓢(WholePlane, ℂ)) :
    wholePlaneRescaleTempered F p ell hell T phi =
      (ell : ℂ) • T (wholePlaneRescaleTest p ell hell phi) := by
  rfl

/-- Weak coordinate differentiation commutes with normalized affine pullback
up to the exact factor `ell⁻¹`. -/
theorem lineDeriv_wholePlaneRescaleTempered
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (T : 𝓢'(WholePlane, F)) (j : Fin 2) :
    ∂_{wholePlaneBasis j} (wholePlaneRescaleTempered F p ell hell T) =
      (ell : ℂ)⁻¹ • wholePlaneRescaleTempered F p ell hell
        (∂_{wholePlaneBasis j} T) := by
  ext phi
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    wholePlaneRescaleTempered_apply_apply]
  change (ell : ℂ) • T
      (-(wholePlaneRescaleTest p ell hell) (∂_{wholePlaneBasis j} phi)) =
    (ell : ℂ)⁻¹ • ((ell : ℂ) • T
      (-∂_{wholePlaneBasis j} (wholePlaneRescaleTest p ell hell phi)))
  rw [lineDeriv_wholePlaneRescaleTest]
  simp only [map_neg, map_smul, smul_neg, smul_smul]
  field_simp [hell.ne']

variable [CompleteSpace F]

/-- The distributional affine pullback agrees exactly with the
normalized affine rescaling of `L²` equivalence classes. -/
theorem wholePlaneL2ToTempered_rescale
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (f : WholePlaneL2 F) :
    wholePlaneL2ToTempered F (wholePlaneRescale F p ell hell f) =
      wholePlaneRescaleTempered F p ell hell
        (wholePlaneL2ToTempered F f) := by
  ext phi
  simp only [wholePlaneL2ToTempered_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply,
    wholePlaneRescaleTempered_apply_apply]
  rw [MeasureTheory.integral_congr_ae (by
    filter_upwards [wholePlaneRescale_coe_ae F p ell hell f] with y hy
    rw [hy])]
  have hchange := MeasureTheory.MeasurePreserving.integral_comp
    (measurePreserving_wholePlaneAffine p ell hell)
    (measurableEmbedding_wholePlaneAffine p ell hell)
    (fun x : WholePlane =>
      ((ell : ℂ)⁻¹ * phi (p + ell • x)) • (f : WholePlane → F) x)
  have hleft :
      (∫ y : WholePlane,
        phi y • ((ell : ℂ)⁻¹ •
          (f : WholePlane → F) (wholePlaneAffine p ell y)) ∂volume) =
      ∫ y : WholePlane,
        ((ell : ℂ)⁻¹ * phi (p + ell • wholePlaneAffine p ell y)) •
          (f : WholePlane → F) (wholePlaneAffine p ell y) ∂volume := by
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun y => ?_)
    change phi y • ((ell : ℂ)⁻¹ •
        (f : WholePlane → F) (wholePlaneAffine p ell y)) =
      ((ell : ℂ)⁻¹ * phi (p + ell • wholePlaneAffine p ell y)) •
        (f : WholePlane → F) (wholePlaneAffine p ell y)
    rw [wholePlaneAffine_forward_left p ell hell]
    simp only [smul_smul]
    congr 1
    ring
  rw [hleft, hchange, MeasureTheory.integral_smul_measure]
  rw [ENNReal.toReal_ofReal (sq_nonneg ell)]
  rw [show (fun x : WholePlane =>
      ((ell : ℂ)⁻¹ * phi (p + ell • x)) • (f : WholePlane → F) x) =
      fun x => (ell : ℂ)⁻¹ •
        (wholePlaneRescaleTest p ell hell phi x •
          (f : WholePlane → F) x) by
    funext x
    rw [wholePlaneRescaleTest_apply]
    simp only [smul_smul]]
  rw [MeasureTheory.integral_smul]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [smul_smul]
  congr 1
  field_simp [hell.ne']
  norm_cast

section H2Scaling

/-- Lift of normalized affine rescaling to the weak `H²` graph. -/
def wholePlaneRescaleH2 (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (u : WholePlaneH2 F) : WholePlaneH2 F :=
  wholePlaneH2OfWeakDerivatives F
    (wholePlaneRescale F p ell hell (wholePlaneH2Embedding F u))
    (fun j => (ell : ℂ)⁻¹ •
      wholePlaneRescale F p ell hell
        (wholePlaneH2FirstDerivative F j u))
    (fun j k => ((ell : ℂ)⁻¹ ^ 2) •
      wholePlaneRescale F p ell hell
        (wholePlaneH2SecondDerivative F j k u))
    (by
      intro j
      rw [wholePlaneL2ToTempered_rescale F p ell hell]
      rw [lineDeriv_wholePlaneRescaleTempered]
      rw [wholePlaneH2_firstDerivative_distribution]
      rw [map_smul, wholePlaneL2ToTempered_rescale])
    (by
      intro j k
      rw [map_smul]
      rw [LineDeriv.lineDerivOp_smul]
      rw [wholePlaneL2ToTempered_rescale F p ell hell]
      rw [lineDeriv_wholePlaneRescaleTempered]
      rw [wholePlaneH2_secondDerivative_distribution]
      rw [map_smul, wholePlaneL2ToTempered_rescale]
      simp only [smul_smul]
      congr 1
      ring)

/-- The physical `L²` field of the `H²` lift is the original `L²`
rescaling. -/
theorem wholePlaneH2Embedding_rescaleH2
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (u : WholePlaneH2 F) :
    wholePlaneH2Embedding F (wholePlaneRescaleH2 F p ell hell u) =
      wholePlaneRescale F p ell hell (wholePlaneH2Embedding F u) := by
  exact wholePlaneH2Embedding_ofWeakDerivatives F _ _ _ _ _

/-- First weak derivatives of the `H²` lift scale by `ell⁻¹`. -/
theorem wholePlaneH2FirstDerivative_rescaleH2
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (u : WholePlaneH2 F) (j : Fin 2) :
    wholePlaneH2FirstDerivative F j
        (wholePlaneRescaleH2 F p ell hell u) =
      (ell : ℂ)⁻¹ • wholePlaneRescale F p ell hell
        (wholePlaneH2FirstDerivative F j u) := by
  exact wholePlaneH2FirstDerivative_ofWeakDerivatives F _ _ _ _ _ j

/-- Ordered second weak derivatives of the `H²` lift scale by `ell⁻²`. -/
theorem wholePlaneH2SecondDerivative_rescaleH2
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (u : WholePlaneH2 F) (j k : Fin 2) :
    wholePlaneH2SecondDerivative F j k
        (wholePlaneRescaleH2 F p ell hell u) =
      ((ell : ℂ)⁻¹ ^ 2) • wholePlaneRescale F p ell hell
        (wholePlaneH2SecondDerivative F j k u) := by
  exact wholePlaneH2SecondDerivative_ofWeakDerivatives F _ _ _ _ _ j k

/-- The transverse weak Laplacian scales by `ell⁻²`. -/
theorem wholePlaneLaplacian_rescaleH2
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (u : WholePlaneH2 F) :
    wholePlaneLaplacian F (wholePlaneRescaleH2 F p ell hell u) =
      ((ell : ℂ)⁻¹ ^ 2) • wholePlaneRescale F p ell hell
        (wholePlaneLaplacian F u) := by
  rw [wholePlaneLaplacian_apply, wholePlaneLaplacian_apply,
    wholePlaneH2SecondDerivative_rescaleH2,
    wholePlaneH2SecondDerivative_rescaleH2]
  have hadd := (wholePlaneRescaleLinear F p ell hell).map_add
    (wholePlaneH2SecondDerivative F 0 0 u)
    (wholePlaneH2SecondDerivative F 1 1 u)
  change wholePlaneRescale F p ell hell
      (wholePlaneH2SecondDerivative F 0 0 u +
        wholePlaneH2SecondDerivative F 1 1 u) =
    wholePlaneRescale F p ell hell
        (wholePlaneH2SecondDerivative F 0 0 u) +
      wholePlaneRescale F p ell hell
        (wholePlaneH2SecondDerivative F 1 1 u) at hadd
  rw [hadd, smul_add]

/-- Exact squared graph norm under normalized affine rescaling in `H²`. -/
theorem norm_sq_wholePlaneRescaleH2
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (u : WholePlaneH2 F) :
    ‖wholePlaneRescaleH2 F p ell hell u‖ ^ 2 =
      ‖wholePlaneH2Embedding F u‖ ^ 2 + ell⁻¹ ^ 2 *
        (‖wholePlaneH2FirstDerivative F 0 u‖ ^ 2 +
          ‖wholePlaneH2FirstDerivative F 1 u‖ ^ 2) + ell⁻¹ ^ 4 *
        (‖wholePlaneH2SecondDerivative F 0 0 u‖ ^ 2 +
          ‖wholePlaneH2SecondDerivative F 0 1 u‖ ^ 2 +
          ‖wholePlaneH2SecondDerivative F 1 0 u‖ ^ 2 +
          ‖wholePlaneH2SecondDerivative F 1 1 u‖ ^ 2) := by
  change ‖(wholePlaneRescaleH2 F p ell hell u).1‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_sum_type, Fintype.sum_option,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  change ‖wholePlaneH2Embedding F
      (wholePlaneRescaleH2 F p ell hell u)‖ ^ 2 +
      (‖wholePlaneH2FirstDerivative F 0
          (wholePlaneRescaleH2 F p ell hell u)‖ ^ 2 +
       ‖wholePlaneH2FirstDerivative F 1
          (wholePlaneRescaleH2 F p ell hell u)‖ ^ 2) +
      ((‖wholePlaneH2SecondDerivative F 0 0
          (wholePlaneRescaleH2 F p ell hell u)‖ ^ 2 +
        ‖wholePlaneH2SecondDerivative F 0 1
          (wholePlaneRescaleH2 F p ell hell u)‖ ^ 2) +
       (‖wholePlaneH2SecondDerivative F 1 0
          (wholePlaneRescaleH2 F p ell hell u)‖ ^ 2 +
        ‖wholePlaneH2SecondDerivative F 1 1
          (wholePlaneRescaleH2 F p ell hell u)‖ ^ 2)) = _
  simp only [wholePlaneH2Embedding_rescaleH2, wholePlaneH2FirstDerivative_rescaleH2,
    wholePlaneH2SecondDerivative_rescaleH2, norm_wholePlaneRescale, norm_smul, norm_pow,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hell]
  ring

/-- Linear map underlying affine rescaling on the weak `H²` graph. -/
def wholePlaneRescaleH2Linear (p : WholePlane) (ell : ℝ)
    (hell : 0 < ell) :
    WholePlaneH2 F →ₗ[ℂ] WholePlaneH2 F where
  toFun := wholePlaneRescaleH2 F p ell hell
  map_add' u v := by
    apply wholePlaneH2Embedding_injective F
    simp only [map_add]
    rw [wholePlaneH2Embedding_rescaleH2,
      wholePlaneH2Embedding_rescaleH2,
      wholePlaneH2Embedding_rescaleH2]
    exact (wholePlaneRescaleLinear F p ell hell).map_add _ _
  map_smul' c u := by
    apply wholePlaneH2Embedding_injective F
    simp only [RingHom.id_apply, map_smul]
    rw [wholePlaneH2Embedding_rescaleH2,
      wholePlaneH2Embedding_rescaleH2]
    exact (wholePlaneRescaleLinear F p ell hell).map_smul c _

/-- Uniform graph-norm bound for affine rescaling on `H²`. -/
theorem norm_wholePlaneRescaleH2_le
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (u : WholePlaneH2 F) :
    ‖wholePlaneRescaleH2 F p ell hell u‖ ≤
      (max 1 ell⁻¹) ^ 2 * ‖u‖ := by
  let M : ℝ := max 1 ell⁻¹
  have ha : 0 ≤ ell⁻¹ := (inv_pos.mpr hell).le
  have hM0 : 0 ≤ M := by
    exact zero_le_one.trans (le_max_left _ _)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMa : ell⁻¹ ≤ M := le_max_right _ _
  have h2 : 1 ≤ M ^ 4 := one_le_pow₀ hM1
  have h2a : ell⁻¹ ^ 2 ≤ M ^ 4 := by
    calc
      ell⁻¹ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ ha hMa 2
      _ ≤ M ^ 2 * M ^ 2 :=
        le_mul_of_one_le_right (sq_nonneg M) (one_le_pow₀ hM1)
      _ = M ^ 4 := by ring
  have h4a : ell⁻¹ ^ 4 ≤ M ^ 4 :=
    pow_le_pow_left₀ ha hMa 4
  rw [← sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
  rw [norm_sq_wholePlaneRescaleH2]
  change _ ≤ (M ^ 2 * ‖u.1‖) ^ 2
  rw [mul_pow, PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_sum_type, Fintype.sum_option,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  have hn (q : WholePlaneJet2Index) : 0 ≤ ‖u.1 q‖ ^ 2 := sq_nonneg _
  simp only [wholePlaneH2Embedding_apply,
    wholePlaneH2FirstDerivative_apply,
    wholePlaneH2SecondDerivative_apply]
  nlinarith [hn (Sum.inl none), hn (Sum.inl (some 0)),
    hn (Sum.inl (some 1)), hn (Sum.inr (0, 0)),
    hn (Sum.inr (0, 1)), hn (Sum.inr (1, 0)),
    hn (Sum.inr (1, 1))]

/-- Bounded affine rescaling on the weak `H²` graph. -/
def wholePlaneRescaleH2CLM (p : WholePlane) (ell : ℝ)
    (hell : 0 < ell) :
    WholePlaneH2 F →L[ℂ] WholePlaneH2 F :=
  (wholePlaneRescaleH2Linear F p ell hell).mkContinuous
    ((max 1 ell⁻¹) ^ 2)
    (norm_wholePlaneRescaleH2_le F p ell hell)

end H2Scaling

section ScalingEquivalences

/-- The explicit inverse `H²` rescaling is a left inverse. -/
theorem wholePlaneRescaleH2_inverse_apply
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (u : WholePlaneH2 F) :
    wholePlaneRescaleH2 F (wholePlaneInverseCenter p ell) ell⁻¹
        (inv_pos.mpr hell) (wholePlaneRescaleH2 F p ell hell u) = u := by
  apply wholePlaneH2Embedding_injective F
  rw [wholePlaneH2Embedding_rescaleH2,
    wholePlaneH2Embedding_rescaleH2,
    wholePlaneRescale_inverse_apply]

/-- The explicit inverse `H²` rescaling is a right inverse. -/
theorem wholePlaneRescaleH2_inverse_apply_right
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (u : WholePlaneH2 F) :
    wholePlaneRescaleH2 F p ell hell
        (wholePlaneRescaleH2 F (wholePlaneInverseCenter p ell) ell⁻¹
          (inv_pos.mpr hell) u) = u := by
  apply wholePlaneH2Embedding_injective F
  rw [wholePlaneH2Embedding_rescaleH2,
    wholePlaneH2Embedding_rescaleH2,
    wholePlaneRescale_inverse_apply_right]

/-- Affine rescaling as a linear equivalence of weak `H²`. -/
def wholePlaneRescaleH2LinearEquiv
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell) :
    LinearEquiv (RingHom.id ℂ) (WholePlaneH2 F) (WholePlaneH2 F) :=
  LinearEquiv.mk (wholePlaneRescaleH2Linear F p ell hell)
    (wholePlaneRescaleH2 F (wholePlaneInverseCenter p ell) ell⁻¹
      (inv_pos.mpr hell))
    (wholePlaneRescaleH2_inverse_apply F p ell hell)
    (wholePlaneRescaleH2_inverse_apply_right F p ell hell)

/-- Affine rescaling as a continuous linear equivalence of weak `H²`. -/
def wholePlaneRescaleH2CLE
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell) :
    WholePlaneH2 F ≃L[ℂ] WholePlaneH2 F :=
  ContinuousLinearEquiv.mk (wholePlaneRescaleH2LinearEquiv F p ell hell)
    (wholePlaneRescaleH2CLM F p ell hell).continuous
    (wholePlaneRescaleH2CLM F (wholePlaneInverseCenter p ell) ell⁻¹
      (inv_pos.mpr hell)).continuous

/-- The bundled `H²` rescaling equivalence acts by the affine rescaling `U_{p,ℓ}` lifted to the
weak `H²` graph. -/
@[simp] theorem wholePlaneRescaleH2CLE_apply
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (u : WholePlaneH2 F) :
    wholePlaneRescaleH2CLE F p ell hell u =
      wholePlaneRescaleH2 F p ell hell u := rfl

/-- The inverse of the `H²` rescaling equivalence is the rescaling with center `-p/ℓ` and scale
`ℓ⁻¹`, the lift of the paper's `U_n⁻¹`. -/
@[simp] theorem wholePlaneRescaleH2CLE_symm_apply
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (u : WholePlaneH2 F) :
    (wholePlaneRescaleH2CLE F p ell hell).symm u =
      wholePlaneRescaleH2 F (wholePlaneInverseCenter p ell) ell⁻¹
        (inv_pos.mpr hell) u := rfl

end ScalingEquivalences

end Distribution

end

end FastDynamo

/-!
## Affine scaling of whole-plane essentially bounded coefficients

This part defines the whole-plane `L∞` spaces, coordinate extraction, and
quotient-level affine pullback on whole-plane `L∞`.

The unnormalized coefficient pullback is

`P_[p,ℓ] a (y) = a ((y - p) / ℓ)`.

It is distinct from the normalized `L²` rescaling
`U_[p,ℓ] f = ℓ⁻¹ P_[p,ℓ] f`.  This distinction is what makes the
transport and stretching factors in Lemma 5.2 cancel exactly.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- Whole-plane `L∞` fields with values in a normed additive group. -/
abbrev WholePlaneLInf (F : Type*) [NormedAddCommGroup F] :=
  Lp F ∞ (volume : Measure WholePlane)

/-- Essentially bounded complex scalar coefficients on the transverse plane. -/
abbrev WholePlaneScalarLInf := WholePlaneLInf ℂ

/-- Essentially bounded complex three-vector coefficients on the transverse plane. -/
abbrev WholePlaneC3LInf := WholePlaneLInf C3

/-- Extract one scalar coordinate from a whole-plane `C3`-valued `L∞` field. -/
def wholePlaneCoordLInf (i : Fin 3) :
    WholePlaneC3LInf →L[ℂ] WholePlaneScalarLInf :=
  (EuclideanSpace.proj i).compLpL ∞ volume

/-- Extract one scalar coordinate from a whole-plane `C3`-valued `L²` field. -/
def wholePlaneCoordL2 (i : Fin 3) :
    WholePlaneC3L2 →L[ℂ] WholePlaneScalarL2 :=
  (EuclideanSpace.proj i).compLpL 2 volume

section

variable (F : Type*) [NormedAddCommGroup F]

/-- Regard an `L∞(volume)` class as an `L∞(ell² · volume)` class.
This is the measure-change stage before affine composition. -/
def wholePlaneChangeMeasureLInf (ell : ℝ)
    (f : WholePlaneLInf F) :
    Lp F ∞ (ENNReal.ofReal (ell ^ 2) • (volume : Measure WholePlane)) :=
  let hf : MemLp (f : WholePlane → F) ∞
      (ENNReal.ofReal (ell ^ 2) • (volume : Measure WholePlane)) :=
    (Lp.memLp f).smul_measure (c := ENNReal.ofReal (ell ^ 2)) (by simp)
  hf.toLp (f : WholePlane → F)

/-- Reinterpreting an `L∞(volume)` class against the scaled measure `ℓ² · volume` does not
change its representative. -/
theorem wholePlaneChangeMeasureLInf_coe_ae (ell : ℝ)
    (f : WholePlaneLInf F) :
    (wholePlaneChangeMeasureLInf F ell f : WholePlane → F) =ᵐ[
      ENNReal.ofReal (ell ^ 2) • (volume : Measure WholePlane)]
      (f : WholePlane → F) := by
  unfold wholePlaneChangeMeasureLInf
  exact MemLp.coeFn_toLp _

/-- Unnormalized affine coefficient pullback
`a ↦ (y ↦ a ((y-p)/ell))` on whole-plane `L∞`. -/
def wholePlaneCoeffPullback (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (f : WholePlaneLInf F) : WholePlaneLInf F :=
  Lp.compMeasurePreserving (wholePlaneAffine p ell)
    (measurePreserving_wholePlaneAffine p ell hell)
    (wholePlaneChangeMeasureLInf F ell f)

/-- The affine coefficient pullback has the composed function `y ↦ f ((y - p) / ℓ)` as an
almost everywhere representative, with no Jacobian normalization factor. -/
theorem wholePlaneCoeffPullback_coe_ae (p : WholePlane) (ell : ℝ)
    (hell : 0 < ell) (f : WholePlaneLInf F) :
    (wholePlaneCoeffPullback F p ell hell f : WholePlane → F) =ᵐ[volume]
      fun y => f (wholePlaneAffine p ell y) := by
  apply (Lp.coeFn_compMeasurePreserving _ _).trans
  exact (measurePreserving_wholePlaneAffine p ell hell).quasiMeasurePreserving.ae_eq_comp
    (wholePlaneChangeMeasureLInf_coe_ae F ell f)

end

end

end FastDynamo

/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.WholePlaneC2
public import LeanPool.FastDynamo.Operator.FormCoercivityConstants

/-!
# The transport-stretching weak form `𝔩_w`

This module builds the sesquilinear form `eq:jump-sectorial-form` of the paper:

`𝔩_w(b,φ) = ⟨∇_⊥b,∇_⊥φ⟩ + N²⟨b,φ⟩ + ⟨w_⊥·∇_⊥b,φ⟩ + iN⟨w₃b,φ⟩`
`            + ∫_{ℝ²} w_⊥·((Div_⊥ b)conj φ + (b·∇_⊥)conj φ)`

on `H¹(ℝ²;ℂ²)`.  The stretching term `(b·∇_⊥)w_⊥` of `eq:horizontal-induction` has been
integrated by parts (§2.1), so no derivative of the velocity occurs and the form is
defined for merely bounded, possibly discontinuous, velocities.

The velocity is typed with the repository's whole-plane `L∞` coefficient type
`WholePlaneC3LInf`, which is also the type of the discontinuous screw flow
`horizontalJumpVelocityLInf` and of the smoothed velocities
(`horizontalSmoothedModeVelocity`).  Its first two coordinates are the horizontal part `w_⊥`
and the third is the axial part `w₃`.

The paper's inner product is linear in its first argument, Mathlib's is conjugate-linear
in its first argument; as everywhere in this development the paper's pairing `⟨f,φ⟩` is
therefore written `inner ℂ (j φ) f`, and a form is an element of `ComplexForm`.

Proved here: boundedness with an explicit constant depending only on `N` and `‖w‖_∞`, the
Gårding inequality `re 𝔩_w(b,b) ≥ ½‖∇_⊥b‖² - C‖b‖²` (`eq:sectorial-estimate-b`), the matching
bound on the imaginary part, and sectoriality of the form after a real shift (§2.1).

The paper displays the imaginary-part bound as `|im 𝔩_w(b,b)| ≤ re 𝔩_w(b,b) + C‖b‖₂²`.  The
Lean bound `horizontalWeakForm_abs_im_le` is instead `|im 𝔩_w(b,b)| ≤ C_im‖b‖²_{H¹}`; combined
with the Gårding inequality it gives `|im 𝔩_α(b,b)| ≤ 2C_im re 𝔩_α(b,b)` for the form `𝔩_α`
shifted by the Gårding constant `α` (`horizontalShiftedWeakForm_sectorial`).  Both say that
`𝔩_w` is sectorial; the Lean sector has slope `2C_im` instead of `1`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HorizontalWeakForm

/-! ## Velocity coordinates -/

/-- A scalar coordinate projection is contractive on the whole-plane `L∞` velocity type. -/
theorem norm_wholePlaneCoordLInf_apply_le (i : Fin 3) (w : WholePlaneC3LInf) :
    ‖wholePlaneCoordLInf i w‖ ≤ ‖w‖ := by
  have hproj : ‖(EuclideanSpace.proj (𝕜 := ℂ) i)‖ ≤ 1 := by
    refine (EuclideanSpace.proj (𝕜 := ℂ) i).opNorm_le_bound zero_le_one ?_
    intro x
    simpa using PiLp.norm_apply_le x i
  have hcoord : ‖wholePlaneCoordLInf i‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le (EuclideanSpace.proj (𝕜 := ℂ) i)).trans hproj
  calc
    ‖wholePlaneCoordLInf i w‖ ≤ ‖wholePlaneCoordLInf i‖ * ‖w‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hcoord (norm_nonneg _)
    _ = ‖w‖ := one_mul _

/-! ## The first-order operators entering the form -/

/-- The transport field `w_⊥·∇_⊥b = Σ_{j<2} w_j ∂_j b` of `eq:jump-sectorial-form`. -/
def horizontalTransport (w : WholePlaneC3LInf) :
    WholePlaneC2H1 →L[ℂ] WholePlaneC2L2 :=
  ∑ j : Fin 2, (scalarVectorMulL2 (E := C2) volume
    (wholePlaneCoordLInf j.castSucc w)).comp (wholePlaneH1FirstDerivative C2 j)

/-- The transverse divergence `Div_⊥ b = Σ_{j<2} ∂_j b_j` of `eq:jump-sectorial-form`. -/
def horizontalDivergence : WholePlaneC2H1 →L[ℂ] WholePlaneScalarL2 :=
  ∑ j : Fin 2, (wholePlaneC2CoordL2 j).comp (wholePlaneH1FirstDerivative C2 j)

/-- The transport field is bounded by the `L∞` velocity norm times the gradient. -/
theorem norm_horizontalTransport_apply_le (w : WholePlaneC3LInf) (b : WholePlaneC2H1) :
    ‖horizontalTransport w b‖ ≤
      ‖w‖ * (‖wholePlaneH1FirstDerivative C2 0 b‖ +
        ‖wholePlaneH1FirstDerivative C2 1 b‖) := by
  have hterm : ∀ j : Fin 2,
      ‖scalarVectorMulL2 (E := C2) volume (wholePlaneCoordLInf j.castSucc w)
          (wholePlaneH1FirstDerivative C2 j b)‖ ≤
        ‖w‖ * ‖wholePlaneH1FirstDerivative C2 j b‖ := by
    intro j
    refine (norm_scalarVectorMulL2_apply_le volume _ _).trans ?_
    exact mul_le_mul_of_nonneg_right
      (norm_wholePlaneCoordLInf_apply_le j.castSucc w) (norm_nonneg _)
  calc
    ‖horizontalTransport w b‖
        = ‖∑ j : Fin 2, scalarVectorMulL2 (E := C2) volume
            (wholePlaneCoordLInf j.castSucc w)
            (wholePlaneH1FirstDerivative C2 j b)‖ := by
      simp [horizontalTransport]
    _ ≤ ∑ j : Fin 2, ‖scalarVectorMulL2 (E := C2) volume
            (wholePlaneCoordLInf j.castSucc w)
            (wholePlaneH1FirstDerivative C2 j b)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 2, ‖w‖ * ‖wholePlaneH1FirstDerivative C2 j b‖ :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = ‖w‖ * (‖wholePlaneH1FirstDerivative C2 0 b‖ +
          ‖wholePlaneH1FirstDerivative C2 1 b‖) := by
      rw [Fin.sum_univ_two]
      ring

/-- The transverse divergence is bounded by the sum of the two gradient components. -/
theorem norm_horizontalDivergence_apply_le (b : WholePlaneC2H1) :
    ‖horizontalDivergence b‖ ≤
      ‖wholePlaneH1FirstDerivative C2 0 b‖ + ‖wholePlaneH1FirstDerivative C2 1 b‖ := by
  calc
    ‖horizontalDivergence b‖
        = ‖∑ j : Fin 2, wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 j b)‖ := by
      simp [horizontalDivergence]
    _ ≤ ∑ j : Fin 2, ‖wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 j b)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin 2, ‖wholePlaneH1FirstDerivative C2 j b‖ :=
      Finset.sum_le_sum fun j _ =>
        norm_wholePlaneC2CoordL2_apply_le j (wholePlaneH1FirstDerivative C2 j b)
    _ = ‖wholePlaneH1FirstDerivative C2 0 b‖ +
          ‖wholePlaneH1FirstDerivative C2 1 b‖ := by
      rw [Fin.sum_univ_two]

/-! ## The five terms of `eq:jump-sectorial-form` -/

/-- The `L²` mass form `(b,φ) ↦ ⟨b,φ⟩`. -/
def horizontalMassForm : ComplexForm WholePlaneC2H1 :=
  (associatedFormPivot (wholePlaneH1Embedding C2)).comp (wholePlaneH1Embedding C2)

/-- The Dirichlet form `(b,φ) ↦ ⟨∇_⊥b,∇_⊥φ⟩`. -/
def horizontalDirichletForm : ComplexForm WholePlaneC2H1 :=
  ∑ j : Fin 2, (associatedFormPivot (wholePlaneH1FirstDerivative C2 j)).comp
    (wholePlaneH1FirstDerivative C2 j)

/-- The diffusion part `⟨∇_⊥b,∇_⊥φ⟩ + N²⟨b,φ⟩` of the form. -/
def horizontalDiffusionForm (N : ℝ) : ComplexForm WholePlaneC2H1 :=
  horizontalDirichletForm + ((N : ℂ) ^ 2) • horizontalMassForm

/-- The transport form `(b,φ) ↦ ⟨w_⊥·∇_⊥b,φ⟩`. -/
def horizontalTransportForm (w : WholePlaneC3LInf) : ComplexForm WholePlaneC2H1 :=
  (associatedFormPivot (wholePlaneH1Embedding C2)).comp (horizontalTransport w)

/-- The axial form `(b,φ) ↦ iN⟨w₃b,φ⟩`. -/
def horizontalAxialForm (N : ℝ) (w : WholePlaneC3LInf) : ComplexForm WholePlaneC2H1 :=
  (Complex.I * (N : ℂ)) •
    ((associatedFormPivot (wholePlaneH1Embedding C2)).comp
      ((scalarVectorMulL2 (E := C2) volume (wholePlaneCoordLInf 2 w)).comp
        (wholePlaneH1Embedding C2)))

/-- The divergence half `(b,φ) ↦ ∫ w_⊥·(Div_⊥ b)conj φ` of the stretching term. -/
def horizontalStretchDivergenceForm (w : WholePlaneC3LInf) : ComplexForm WholePlaneC2H1 :=
  ∑ j : Fin 2,
    (associatedFormPivot ((wholePlaneC2CoordL2 j).comp (wholePlaneH1Embedding C2))).comp
      ((scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w)).comp
        horizontalDivergence)

/-- The gradient half `(b,φ) ↦ ∫ w_⊥·(b·∇_⊥)conj φ` of the stretching term. -/
def horizontalStretchGradientForm (w : WholePlaneC3LInf) : ComplexForm WholePlaneC2H1 :=
  ∑ j : Fin 2, ∑ k : Fin 2,
    (associatedFormPivot
        ((wholePlaneC2CoordL2 j).comp (wholePlaneH1FirstDerivative C2 k))).comp
      ((scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w)).comp
        ((wholePlaneC2CoordL2 k).comp (wholePlaneH1Embedding C2)))

/-- The transport-stretching weak form `𝔩_w` of `eq:jump-sectorial-form`. -/
def horizontalWeakForm (N : ℝ) (w : WholePlaneC3LInf) : ComplexForm WholePlaneC2H1 :=
  horizontalDiffusionForm N + horizontalTransportForm w + horizontalAxialForm N w +
    horizontalStretchDivergenceForm w + horizontalStretchGradientForm w

/-! ## Evaluation -/

/-- Evaluation of the mass form. -/
@[simp] theorem horizontalMassForm_apply (b phi : WholePlaneC2H1) :
    horizontalMassForm b phi =
      inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneH1Embedding C2 b) :=
  rfl

/-- Evaluation of the Dirichlet form. -/
theorem horizontalDirichletForm_apply (b phi : WholePlaneC2H1) :
    horizontalDirichletForm b phi =
      ∑ j : Fin 2, inner ℂ (wholePlaneH1FirstDerivative C2 j phi)
        (wholePlaneH1FirstDerivative C2 j b) := by
  simp [horizontalDirichletForm]

/-- Evaluation of the diffusion form. -/
theorem horizontalDiffusionForm_apply (N : ℝ) (b phi : WholePlaneC2H1) :
    horizontalDiffusionForm N b phi =
      (∑ j : Fin 2, inner ℂ (wholePlaneH1FirstDerivative C2 j phi)
          (wholePlaneH1FirstDerivative C2 j b)) +
        (N : ℂ) ^ 2 *
          inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneH1Embedding C2 b) := by
  simp [horizontalDiffusionForm, horizontalDirichletForm_apply]

/-- Evaluation of the transport form. -/
@[simp] theorem horizontalTransportForm_apply (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    horizontalTransportForm w b phi =
      inner ℂ (wholePlaneH1Embedding C2 phi) (horizontalTransport w b) :=
  rfl

/-- Evaluation of the axial form. -/
@[simp] theorem horizontalAxialForm_apply (N : ℝ) (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    horizontalAxialForm N w b phi =
      Complex.I * (N : ℂ) *
        inner ℂ (wholePlaneH1Embedding C2 phi)
          (scalarVectorMulL2 volume (wholePlaneCoordLInf 2 w)
            (wholePlaneH1Embedding C2 b)) :=
  rfl

/-- Evaluation of the divergence half of the stretching term. -/
theorem horizontalStretchDivergenceForm_apply (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    horizontalStretchDivergenceForm w b phi =
      ∑ j : Fin 2, inner ℂ (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 phi))
        (scalarVectorMulL2 volume (wholePlaneCoordLInf j.castSucc w)
          (horizontalDivergence b)) := by
  simp [horizontalStretchDivergenceForm]

/-- Evaluation of the gradient half of the stretching term. -/
theorem horizontalStretchGradientForm_apply (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    horizontalStretchGradientForm w b phi =
      ∑ j : Fin 2, ∑ k : Fin 2,
        inner ℂ (wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 k phi))
          (scalarVectorMulL2 volume (wholePlaneCoordLInf j.castSucc w)
            (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b))) := by
  simp [horizontalStretchGradientForm]

/-- Evaluation of `𝔩_w`, the five terms of `eq:jump-sectorial-form`. -/
theorem horizontalWeakForm_apply (N : ℝ) (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    horizontalWeakForm N w b phi =
      horizontalDiffusionForm N b phi + horizontalTransportForm w b phi +
        horizontalAxialForm N w b phi + horizontalStretchDivergenceForm w b phi +
        horizontalStretchGradientForm w b phi :=
  rfl

/-! ## Elementary complex-part inequalities

Both are Mathlib's `RCLike.abs_im_le_norm` and `RCLike.abs_re_le_norm`, restated with the
`Complex.re`/`Complex.im` spelling that the estimates below match syntactically.
-/

/-- The imaginary part of a complex number is bounded by its modulus.  This is
`RCLike.abs_im_le_norm` with `Complex.im` in place of `RCLike.im`. -/
private theorem abs_im_le_norm (z : ℂ) : |z.im| ≤ ‖z‖ := by
  simpa using RCLike.abs_im_le_norm z

/-- The real part of a complex number is bounded below by minus its modulus.  This is
`RCLike.abs_re_le_norm` with `Complex.re` in place of `RCLike.re`. -/
private theorem neg_norm_le_re (z : ℂ) : -‖z‖ ≤ z.re :=
  (abs_le.1 (RCLike.abs_re_le_norm z)).1

/-- The self inner product has real part the squared norm. -/
theorem inner_self_re (x : WholePlaneC2L2) : (inner ℂ x x : ℂ).re = ‖x‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The self inner product is real. -/
theorem inner_self_im (x : WholePlaneC2L2) : (inner ℂ x x : ℂ).im = 0 := by
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Monotone three-factor product bound, used to turn each sharp form estimate into the
crude graph-norm estimate. -/
private theorem mul_mul_le_of_le {c x y B P : ℝ} (hc : 0 ≤ c) (hy0 : 0 ≤ y)
    (hB : 0 ≤ B) (hx : x ≤ B) (hy : y ≤ P) : c * x * y ≤ c * (B * P) := by
  have h1 : c * x ≤ c * B := mul_le_mul_of_nonneg_left hx hc
  have h2 : c * x * y ≤ c * B * y := mul_le_mul_of_nonneg_right h1 hy0
  have h3 : c * B * y ≤ c * B * P := mul_le_mul_of_nonneg_left hy (mul_nonneg hc hB)
  calc
    c * x * y ≤ c * B * y := h2
    _ ≤ c * B * P := h3
    _ = c * (B * P) := by ring

/-! ## Sharp bounds for the individual terms -/

/-- The squared `L²` norm of the transverse gradient, `‖∇_⊥b‖²`. -/
def horizontalGradientNormSq (b : WholePlaneC2H1) : ℝ :=
  ‖wholePlaneH1FirstDerivative C2 0 b‖ ^ 2 + ‖wholePlaneH1FirstDerivative C2 1 b‖ ^ 2

/-- The squared `H¹` graph norm splits as the squared `L²` norm plus the squared gradient
norm. -/
theorem norm_sq_eq_gradientNormSq_add (b : WholePlaneC2H1) :
    ‖b‖ ^ 2 = ‖wholePlaneH1Embedding C2 b‖ ^ 2 + horizontalGradientNormSq b := by
  rw [norm_sq_wholePlaneC2H1 b, horizontalGradientNormSq]

/-- The transport term is bounded by the velocity times the gradient of the input and the
`L²` norm of the test field. -/
theorem norm_horizontalTransportForm_apply_le (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    ‖horizontalTransportForm w b phi‖ ≤
      ‖w‖ * (‖wholePlaneH1FirstDerivative C2 0 b‖ +
          ‖wholePlaneH1FirstDerivative C2 1 b‖) *
        ‖wholePlaneH1Embedding C2 phi‖ := by
  rw [horizontalTransportForm_apply]
  calc
    ‖inner ℂ (wholePlaneH1Embedding C2 phi) (horizontalTransport w b)‖
        ≤ ‖wholePlaneH1Embedding C2 phi‖ * ‖horizontalTransport w b‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖wholePlaneH1Embedding C2 phi‖ *
          (‖w‖ * (‖wholePlaneH1FirstDerivative C2 0 b‖ +
            ‖wholePlaneH1FirstDerivative C2 1 b‖)) :=
      mul_le_mul_of_nonneg_left (norm_horizontalTransport_apply_le w b) (norm_nonneg _)
    _ = ‖w‖ * (‖wholePlaneH1FirstDerivative C2 0 b‖ +
          ‖wholePlaneH1FirstDerivative C2 1 b‖) *
          ‖wholePlaneH1Embedding C2 phi‖ := by ring

/-- The axial term is bounded by `|N| ‖w‖_∞` times the two `L²` norms. -/
theorem norm_horizontalAxialForm_apply_le (N : ℝ) (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    ‖horizontalAxialForm N w b phi‖ ≤
      |N| * ‖w‖ * ‖wholePlaneH1Embedding C2 b‖ * ‖wholePlaneH1Embedding C2 phi‖ := by
  rw [horizontalAxialForm_apply, norm_mul, norm_mul]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hN : ‖(N : ℂ)‖ = |N| := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hI, hN, one_mul]
  have hmul : ‖scalarVectorMulL2 volume (wholePlaneCoordLInf 2 w)
      (wholePlaneH1Embedding C2 b)‖ ≤ ‖w‖ * ‖wholePlaneH1Embedding C2 b‖ :=
    (norm_scalarVectorMulL2_apply_le volume _ _).trans
      (mul_le_mul_of_nonneg_right (norm_wholePlaneCoordLInf_apply_le 2 w) (norm_nonneg _))
  calc
    |N| * ‖inner ℂ (wholePlaneH1Embedding C2 phi)
        (scalarVectorMulL2 volume (wholePlaneCoordLInf 2 w)
          (wholePlaneH1Embedding C2 b))‖
        ≤ |N| * (‖wholePlaneH1Embedding C2 phi‖ *
            (‖w‖ * ‖wholePlaneH1Embedding C2 b‖)) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg N)
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left hmul (norm_nonneg _))
    _ = |N| * ‖w‖ * ‖wholePlaneH1Embedding C2 b‖ *
          ‖wholePlaneH1Embedding C2 phi‖ := by ring

/-- The divergence half of the stretching term is bounded by twice the velocity times the
gradient of the input and the `L²` norm of the test field. -/
theorem norm_horizontalStretchDivergenceForm_apply_le (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    ‖horizontalStretchDivergenceForm w b phi‖ ≤
      2 * ‖w‖ * (‖wholePlaneH1FirstDerivative C2 0 b‖ +
          ‖wholePlaneH1FirstDerivative C2 1 b‖) *
        ‖wholePlaneH1Embedding C2 phi‖ := by
  rw [horizontalStretchDivergenceForm_apply]
  have hterm : ∀ j : Fin 2,
      ‖inner ℂ (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 phi))
          (scalarVectorMulL2 volume (wholePlaneCoordLInf j.castSucc w)
            (horizontalDivergence b))‖ ≤
        ‖wholePlaneH1Embedding C2 phi‖ *
          (‖w‖ * (‖wholePlaneH1FirstDerivative C2 0 b‖ +
            ‖wholePlaneH1FirstDerivative C2 1 b‖)) := by
    intro j
    refine (norm_inner_le_norm _ _).trans ?_
    refine mul_le_mul (norm_wholePlaneC2CoordL2_apply_le j _) ?_ (norm_nonneg _)
      (norm_nonneg _)
    refine (norm_scalarVectorMulL2_apply_le volume _ _).trans ?_
    exact mul_le_mul (norm_wholePlaneCoordLInf_apply_le j.castSucc w)
      (norm_horizontalDivergence_apply_le b) (norm_nonneg _) (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hterm j).trans_eq ?_
  rw [Fin.sum_univ_two]
  ring

/-- The gradient half of the stretching term is bounded by twice the velocity times the `L²`
norm of the input and the gradient of the test field. -/
theorem norm_horizontalStretchGradientForm_apply_le (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    ‖horizontalStretchGradientForm w b phi‖ ≤
      2 * ‖w‖ * ‖wholePlaneH1Embedding C2 b‖ *
        (‖wholePlaneH1FirstDerivative C2 0 phi‖ +
          ‖wholePlaneH1FirstDerivative C2 1 phi‖) := by
  rw [horizontalStretchGradientForm_apply]
  have hterm : ∀ j k : Fin 2,
      ‖inner ℂ (wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 k phi))
          (scalarVectorMulL2 volume (wholePlaneCoordLInf j.castSucc w)
            (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b)))‖ ≤
        ‖wholePlaneH1FirstDerivative C2 k phi‖ *
          (‖w‖ * ‖wholePlaneH1Embedding C2 b‖) := by
    intro j k
    refine (norm_inner_le_norm _ _).trans ?_
    refine mul_le_mul (norm_wholePlaneC2CoordL2_apply_le j _) ?_ (norm_nonneg _)
      (norm_nonneg _)
    refine (norm_scalarVectorMulL2_apply_le volume _ _).trans ?_
    exact mul_le_mul (norm_wholePlaneCoordLInf_apply_le j.castSucc w)
      (norm_wholePlaneC2CoordL2_apply_le k _) (norm_nonneg _) (norm_nonneg _)
  have hinner : ∀ j : Fin 2,
      ‖∑ k : Fin 2, inner ℂ (wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 k phi))
          (scalarVectorMulL2 volume (wholePlaneCoordLInf j.castSucc w)
            (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b)))‖ ≤
        ‖w‖ * ‖wholePlaneH1Embedding C2 b‖ *
          (‖wholePlaneH1FirstDerivative C2 0 phi‖ +
            ‖wholePlaneH1FirstDerivative C2 1 phi‖) := by
    intro j
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hterm j k).trans_eq ?_
    rw [Fin.sum_univ_two]
    ring
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hinner j).trans_eq ?_
  rw [Fin.sum_univ_two]
  ring

/-! ## Boundedness on `H¹` -/

/-- The explicit constant in the boundedness estimate for `𝔩_w`; it depends only on `N` and
on `‖w‖_∞`, as stated in §2.1 of the paper. -/
def horizontalFormBound (N : ℝ) (w : WholePlaneC3LInf) : ℝ :=
  2 + N ^ 2 + |N| * ‖w‖ + 10 * ‖w‖

/-- Boundedness of the Dirichlet form on `H¹`. -/
theorem norm_horizontalDirichletForm_apply_le (b phi : WholePlaneC2H1) :
    ‖horizontalDirichletForm b phi‖ ≤ 2 * (‖b‖ * ‖phi‖) := by
  rw [horizontalDirichletForm_apply]
  have hterm : ∀ j : Fin 2,
      ‖inner ℂ (wholePlaneH1FirstDerivative C2 j phi)
        (wholePlaneH1FirstDerivative C2 j b)‖ ≤ ‖b‖ * ‖phi‖ := by
    intro j
    refine (norm_inner_le_norm _ _).trans ?_
    rw [mul_comm ‖b‖ ‖phi‖]
    exact mul_le_mul (norm_wholePlaneH1FirstDerivative_le C2 phi j)
      (norm_wholePlaneH1FirstDerivative_le C2 b j) (norm_nonneg _) (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hterm j).trans_eq ?_
  rw [Fin.sum_univ_two]
  ring

/-- Boundedness of the mass form on `H¹`. -/
theorem norm_horizontalMassForm_apply_le (b phi : WholePlaneC2H1) :
    ‖horizontalMassForm b phi‖ ≤ ‖b‖ * ‖phi‖ := by
  rw [horizontalMassForm_apply]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [mul_comm ‖b‖ ‖phi‖]
  exact mul_le_mul (norm_wholePlaneH1Embedding_le C2 phi)
    (norm_wholePlaneH1Embedding_le C2 b) (norm_nonneg _) (norm_nonneg _)

/-- Boundedness of the diffusion part on `H¹`. -/
theorem norm_horizontalDiffusionForm_apply_le (N : ℝ) (b phi : WholePlaneC2H1) :
    ‖horizontalDiffusionForm N b phi‖ ≤ (2 + N ^ 2) * (‖b‖ * ‖phi‖) := by
  have hsplit : horizontalDiffusionForm N b phi =
      horizontalDirichletForm b phi + (N : ℂ) ^ 2 * horizontalMassForm b phi := by
    rw [horizontalDiffusionForm_apply, horizontalDirichletForm_apply,
      horizontalMassForm_apply]
  have hNsq : ‖((N : ℂ) ^ 2)‖ = N ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have key : ∀ z1 z2 : ℂ, ‖z1‖ ≤ 2 * (‖b‖ * ‖phi‖) → ‖z2‖ ≤ ‖b‖ * ‖phi‖ →
      ‖z1 + (N : ℂ) ^ 2 * z2‖ ≤ (2 + N ^ 2) * (‖b‖ * ‖phi‖) := by
    intro z1 z2 h1 h2
    have hz : ‖z1 + (N : ℂ) ^ 2 * z2‖ ≤ ‖z1‖ + N ^ 2 * ‖z2‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, hNsq]
    have h3 : N ^ 2 * ‖z2‖ ≤ N ^ 2 * (‖b‖ * ‖phi‖) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg N)
    calc
      ‖z1 + (N : ℂ) ^ 2 * z2‖ ≤ ‖z1‖ + N ^ 2 * ‖z2‖ := hz
      _ ≤ 2 * (‖b‖ * ‖phi‖) + N ^ 2 * (‖b‖ * ‖phi‖) := add_le_add h1 h3
      _ = (2 + N ^ 2) * (‖b‖ * ‖phi‖) := by ring
  rw [hsplit]
  exact key _ _ (norm_horizontalDirichletForm_apply_le b phi)
    (norm_horizontalMassForm_apply_le b phi)

/-- Crude graph-norm bound for the transport term. -/
theorem norm_horizontalTransportForm_apply_le' (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    ‖horizontalTransportForm w b phi‖ ≤ 2 * ‖w‖ * (‖b‖ * ‖phi‖) := by
  have hgradb : ‖wholePlaneH1FirstDerivative C2 0 b‖ +
      ‖wholePlaneH1FirstDerivative C2 1 b‖ ≤ 2 * ‖b‖ := by
    have h0 := norm_wholePlaneH1FirstDerivative_le C2 b 0
    have h1 := norm_wholePlaneH1FirstDerivative_le C2 b 1
    linarith
  refine (norm_horizontalTransportForm_apply_le w b phi).trans ?_
  have hkey := mul_mul_le_of_le (c := ‖w‖) (norm_nonneg w)
    (norm_nonneg (wholePlaneH1Embedding C2 phi)) (by positivity : (0 : ℝ) ≤ 2 * ‖b‖)
    hgradb (norm_wholePlaneH1Embedding_le C2 phi)
  calc
    ‖w‖ * (‖wholePlaneH1FirstDerivative C2 0 b‖ +
        ‖wholePlaneH1FirstDerivative C2 1 b‖) * ‖wholePlaneH1Embedding C2 phi‖
        ≤ ‖w‖ * (2 * ‖b‖ * ‖phi‖) := hkey
    _ = 2 * ‖w‖ * (‖b‖ * ‖phi‖) := by ring

/-- Crude graph-norm bound for the axial term. -/
theorem norm_horizontalAxialForm_apply_le' (N : ℝ) (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    ‖horizontalAxialForm N w b phi‖ ≤ |N| * ‖w‖ * (‖b‖ * ‖phi‖) := by
  refine (norm_horizontalAxialForm_apply_le N w b phi).trans ?_
  exact mul_mul_le_of_le (c := |N| * ‖w‖) (mul_nonneg (abs_nonneg N) (norm_nonneg w))
    (norm_nonneg (wholePlaneH1Embedding C2 phi)) (norm_nonneg b)
    (norm_wholePlaneH1Embedding_le C2 b) (norm_wholePlaneH1Embedding_le C2 phi)

/-- Crude graph-norm bound for the divergence half of the stretching term. -/
theorem norm_horizontalStretchDivergenceForm_apply_le' (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    ‖horizontalStretchDivergenceForm w b phi‖ ≤ 4 * ‖w‖ * (‖b‖ * ‖phi‖) := by
  have hgradb : ‖wholePlaneH1FirstDerivative C2 0 b‖ +
      ‖wholePlaneH1FirstDerivative C2 1 b‖ ≤ 2 * ‖b‖ := by
    have h0 := norm_wholePlaneH1FirstDerivative_le C2 b 0
    have h1 := norm_wholePlaneH1FirstDerivative_le C2 b 1
    linarith
  refine (norm_horizontalStretchDivergenceForm_apply_le w b phi).trans ?_
  have hkey := mul_mul_le_of_le (c := 2 * ‖w‖) (by positivity)
    (norm_nonneg (wholePlaneH1Embedding C2 phi)) (by positivity : (0 : ℝ) ≤ 2 * ‖b‖)
    hgradb (norm_wholePlaneH1Embedding_le C2 phi)
  calc
    2 * ‖w‖ * (‖wholePlaneH1FirstDerivative C2 0 b‖ +
        ‖wholePlaneH1FirstDerivative C2 1 b‖) * ‖wholePlaneH1Embedding C2 phi‖
        ≤ 2 * ‖w‖ * (2 * ‖b‖ * ‖phi‖) := hkey
    _ = 4 * ‖w‖ * (‖b‖ * ‖phi‖) := by ring

/-- Crude graph-norm bound for the gradient half of the stretching term. -/
theorem norm_horizontalStretchGradientForm_apply_le' (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    ‖horizontalStretchGradientForm w b phi‖ ≤ 4 * ‖w‖ * (‖b‖ * ‖phi‖) := by
  have hgradp : ‖wholePlaneH1FirstDerivative C2 0 phi‖ +
      ‖wholePlaneH1FirstDerivative C2 1 phi‖ ≤ 2 * ‖phi‖ := by
    have h0 := norm_wholePlaneH1FirstDerivative_le C2 phi 0
    have h1 := norm_wholePlaneH1FirstDerivative_le C2 phi 1
    linarith
  refine (norm_horizontalStretchGradientForm_apply_le w b phi).trans ?_
  have hkey := mul_mul_le_of_le (c := 2 * ‖w‖) (by positivity)
    (by positivity : (0 : ℝ) ≤ ‖wholePlaneH1FirstDerivative C2 0 phi‖ +
      ‖wholePlaneH1FirstDerivative C2 1 phi‖)
    (norm_nonneg b) (norm_wholePlaneH1Embedding_le C2 b) hgradp
  calc
    2 * ‖w‖ * ‖wholePlaneH1Embedding C2 b‖ *
        (‖wholePlaneH1FirstDerivative C2 0 phi‖ +
          ‖wholePlaneH1FirstDerivative C2 1 phi‖)
        ≤ 2 * ‖w‖ * (‖b‖ * (2 * ‖phi‖)) := hkey
    _ = 4 * ‖w‖ * (‖b‖ * ‖phi‖) := by ring

/-- Arithmetic core of the boundedness estimate. -/
private theorem weakForm_bound_core {N M B P : ℝ} (zD zT zA zSD zSG : ℂ)
    (h1 : ‖zD‖ ≤ (2 + N ^ 2) * (B * P)) (h2 : ‖zT‖ ≤ 2 * M * (B * P))
    (h3 : ‖zA‖ ≤ |N| * M * (B * P)) (h4 : ‖zSD‖ ≤ 4 * M * (B * P))
    (h5 : ‖zSG‖ ≤ 4 * M * (B * P)) :
    ‖zD + zT + zA + zSD + zSG‖ ≤ (2 + N ^ 2 + |N| * M + 10 * M) * B * P := by
  have hsum : ‖zD + zT + zA + zSD + zSG‖ ≤ ‖zD‖ + ‖zT‖ + ‖zA‖ + ‖zSD‖ + ‖zSG‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  have hexpand : (2 + N ^ 2 + |N| * M + 10 * M) * B * P =
      (2 + N ^ 2) * (B * P) + 2 * M * (B * P) + |N| * M * (B * P) + 4 * M * (B * P) +
        4 * M * (B * P) := by ring
  rw [hexpand]
  linarith

/-- `𝔩_w` is bounded on `H¹(ℝ²;ℂ²)` with a constant depending only on `N` and `‖w‖_∞`
(§2.1 of the paper). -/
theorem norm_horizontalWeakForm_apply_le (N : ℝ) (w : WholePlaneC3LInf)
    (b phi : WholePlaneC2H1) :
    ‖horizontalWeakForm N w b phi‖ ≤ horizontalFormBound N w * ‖b‖ * ‖phi‖ := by
  have hval : ‖horizontalWeakForm N w b phi‖ =
      ‖horizontalDiffusionForm N b phi + horizontalTransportForm w b phi +
        horizontalAxialForm N w b phi + horizontalStretchDivergenceForm w b phi +
        horizontalStretchGradientForm w b phi‖ :=
    congrArg _ (horizontalWeakForm_apply N w b phi)
  have hcore := weakForm_bound_core (N := N) (M := ‖w‖) (B := ‖b‖) (P := ‖phi‖)
    (horizontalDiffusionForm N b phi) (horizontalTransportForm w b phi)
    (horizontalAxialForm N w b phi) (horizontalStretchDivergenceForm w b phi)
    (horizontalStretchGradientForm w b phi)
    (norm_horizontalDiffusionForm_apply_le N b phi)
    (norm_horizontalTransportForm_apply_le' w b phi)
    (norm_horizontalAxialForm_apply_le' N w b phi)
    (norm_horizontalStretchDivergenceForm_apply_le' w b phi)
    (norm_horizontalStretchGradientForm_apply_le' w b phi)
  simp only [horizontalFormBound]
  linarith [hval, hcore]

/-! ## Gårding inequality, imaginary-part control, sectoriality -/

/-- Real part of the diffusion form on the diagonal. -/
theorem horizontalDiffusionForm_self_re (N : ℝ) (b : WholePlaneC2H1) :
    (horizontalDiffusionForm N b b).re =
      horizontalGradientNormSq b + N ^ 2 * ‖wholePlaneH1Embedding C2 b‖ ^ 2 := by
  simp only [horizontalDiffusionForm_apply, Fin.sum_univ_two, horizontalGradientNormSq,
    ← Complex.ofReal_pow, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, inner_self_re, inner_self_im]
  ring

/-- The diffusion form is real on the diagonal. -/
theorem horizontalDiffusionForm_self_im (N : ℝ) (b : WholePlaneC2H1) :
    (horizontalDiffusionForm N b b).im = 0 := by
  simp only [horizontalDiffusionForm_apply, Fin.sum_univ_two,
    ← Complex.ofReal_pow, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, inner_self_im, inner_self_re]
  ring

/-- The three velocity terms carrying a transverse derivative obey one common bound on the
diagonal. -/
theorem norm_horizontalStretchTransport_self_le (w : WholePlaneC3LInf)
    (b : WholePlaneC2H1) :
    ‖horizontalTransportForm w b b‖ + ‖horizontalStretchDivergenceForm w b b‖ +
        ‖horizontalStretchGradientForm w b b‖ ≤
      5 * ‖w‖ * ‖wholePlaneH1Embedding C2 b‖ *
        (‖wholePlaneH1FirstDerivative C2 0 b‖ +
          ‖wholePlaneH1FirstDerivative C2 1 b‖) := by
  have h1 := norm_horizontalTransportForm_apply_le w b b
  have h2 := norm_horizontalStretchDivergenceForm_apply_le w b b
  have h3 := norm_horizontalStretchGradientForm_apply_le w b b
  nlinarith [h1, h2, h3]

/-- The explicit Gårding constant of `eq:jump-sectorial-form`, depending only on `N` and
`‖w‖_∞`. -/
def horizontalGardingConstant (N : ℝ) (w : WholePlaneC3LInf) : ℝ :=
  50 * ‖w‖ ^ 2 + |N| * ‖w‖

/-- The Gårding constant is nonnegative. -/
theorem horizontalGardingConstant_nonneg (N : ℝ) (w : WholePlaneC3LInf) :
    0 ≤ horizontalGardingConstant N w := by
  have h2 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have h3 : 0 ≤ |N| * ‖w‖ := mul_nonneg (abs_nonneg N) (norm_nonneg w)
  unfold horizontalGardingConstant
  linarith

/-- Real-part splitting of `𝔩_w` on the diagonal. -/
theorem horizontalWeakForm_self_re (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) :
    (horizontalWeakForm N w b b).re =
      (horizontalDiffusionForm N b b).re + (horizontalTransportForm w b b).re +
        (horizontalAxialForm N w b b).re +
        (horizontalStretchDivergenceForm w b b).re +
        (horizontalStretchGradientForm w b b).re := by
  rfl

/-- Imaginary-part splitting of `𝔩_w` on the diagonal. -/
private theorem horizontalWeakForm_self_im_split (N : ℝ) (w : WholePlaneC3LInf)
    (b : WholePlaneC2H1) :
    (horizontalWeakForm N w b b).im =
      (horizontalDiffusionForm N b b).im + (horizontalTransportForm w b b).im +
        (horizontalAxialForm N w b b).im +
        (horizontalStretchDivergenceForm w b b).im +
        (horizontalStretchGradientForm w b b).im :=
  rfl

/-- Imaginary-part splitting of `𝔩_w` on the diagonal, the diffusion part being real. -/
theorem horizontalWeakForm_self_im (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) :
    (horizontalWeakForm N w b b).im =
      (horizontalTransportForm w b b).im + (horizontalAxialForm N w b b).im +
        (horizontalStretchDivergenceForm w b b).im +
        (horizontalStretchGradientForm w b b).im := by
  have h := horizontalWeakForm_self_im_split N w b
  have h0 := horizontalDiffusionForm_self_im N b
  linarith [h, h0]

/-- Arithmetic core of the Gårding inequality: Young's inequality in the four real
quantities `‖∂₀b‖`, `‖∂₁b‖`, `‖b‖₂` and `‖w‖_∞`. -/
private theorem garding_core {G0 G1 M m T A SD SG nT nA nSD nSG N : ℝ}
    (hlow : nT + nSD + nSG ≤ 5 * M * m * (G0 + G1))
    (haxn : nA ≤ |N| * M * m * m)
    (hT : -nT ≤ T) (hA : -nA ≤ A) (hSD : -nSD ≤ SD) (hSG : -nSG ≤ SG) :
    1 / 2 * (G0 ^ 2 + G1 ^ 2) - (50 * M ^ 2 + |N| * M) * m ^ 2 ≤
      G0 ^ 2 + G1 ^ 2 + N ^ 2 * m ^ 2 + T + A + SD + SG := by
  have hyoung : 5 * M * m * (G0 + G1) ≤ 1 / 4 * (G0 ^ 2 + G1 ^ 2) + 50 * M ^ 2 * m ^ 2 := by
    nlinarith [sq_nonneg (G0 / 2 - 5 * M * m), sq_nonneg (G1 / 2 - 5 * M * m)]
  nlinarith [hlow, haxn, hT, hA, hSD, hSG, hyoung, sq_nonneg G0, sq_nonneg G1,
    sq_nonneg (N * m)]

/-- The Gårding inequality `re 𝔩_w(b,b) ≥ ½‖∇_⊥b‖² - C‖b‖²` of `eq:sectorial-estimate-b`,
proved by Young's inequality. -/
theorem horizontalWeakForm_garding (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) :
    1 / 2 * horizontalGradientNormSq b -
        horizontalGardingConstant N w * ‖wholePlaneH1Embedding C2 b‖ ^ 2 ≤
      (horizontalWeakForm N w b b).re := by
  have hre := horizontalWeakForm_self_re N w b
  have hdiff := horizontalDiffusionForm_self_re N b
  have hcore := garding_core (G0 := ‖wholePlaneH1FirstDerivative C2 0 b‖)
    (G1 := ‖wholePlaneH1FirstDerivative C2 1 b‖) (M := ‖w‖)
    (m := ‖wholePlaneH1Embedding C2 b‖) (N := N)
    (norm_horizontalStretchTransport_self_le w b)
    (norm_horizontalAxialForm_apply_le N w b b) (neg_norm_le_re _) (neg_norm_le_re _)
    (neg_norm_le_re _) (neg_norm_le_re _)
  simp only [horizontalGradientNormSq] at hdiff
  simp only [horizontalGardingConstant, horizontalGradientNormSq]
  linarith [hre, hdiff, hcore]

/-- The explicit constant controlling the imaginary part of `𝔩_w` on the diagonal. -/
def horizontalImaginaryConstant (N : ℝ) (w : WholePlaneC3LInf) : ℝ :=
  5 * ‖w‖ + |N| * ‖w‖

/-- The imaginary-part constant is nonnegative. -/
theorem horizontalImaginaryConstant_nonneg (N : ℝ) (w : WholePlaneC3LInf) :
    0 ≤ horizontalImaginaryConstant N w := by
  have h3 : 0 ≤ |N| * ‖w‖ := mul_nonneg (abs_nonneg N) (norm_nonneg w)
  have h := norm_nonneg w
  unfold horizontalImaginaryConstant
  linarith

/-- The imaginary part of `𝔩_w` on the diagonal is bounded by the four velocity terms. -/
private theorem abs_im_horizontalWeakForm_self_le (N : ℝ) (w : WholePlaneC3LInf)
    (b : WholePlaneC2H1) :
    |(horizontalWeakForm N w b b).im| ≤
      ‖horizontalTransportForm w b b‖ + ‖horizontalAxialForm N w b b‖ +
        ‖horizontalStretchDivergenceForm w b b‖ +
        ‖horizontalStretchGradientForm w b b‖ := by
  rw [horizontalWeakForm_self_im]
  refine (abs_add_le _ _).trans (add_le_add ?_ (abs_im_le_norm _))
  refine (abs_add_le _ _).trans (add_le_add ?_ (abs_im_le_norm _))
  exact (abs_add_le _ _).trans (add_le_add (abs_im_le_norm _) (abs_im_le_norm _))

/-- Arithmetic core of the imaginary-part estimate. -/
private theorem imaginary_core {G0 G1 M m I nT nA nSD nSG N : ℝ}
    (hstep : I ≤ nT + nA + nSD + nSG)
    (hlow : nT + nSD + nSG ≤ 5 * M * m * (G0 + G1))
    (haxn : nA ≤ |N| * M * m * m)
    (hM : 0 ≤ M) :
    I ≤ (5 * M + |N| * M) * (m ^ 2 + (G0 ^ 2 + G1 ^ 2)) := by
  nlinarith [hstep, hlow, haxn, hM, abs_nonneg N,
    mul_nonneg hM (sq_nonneg (m - G0)), mul_nonneg hM (sq_nonneg (m - G1)),
    mul_nonneg hM (sq_nonneg G0), mul_nonneg hM (sq_nonneg G1),
    mul_nonneg (mul_nonneg (abs_nonneg N) hM) (sq_nonneg G0),
    mul_nonneg (mul_nonneg (abs_nonneg N) hM) (sq_nonneg G1)]

/-- The same first-order estimates control the imaginary part of `𝔩_w` on the diagonal by the
full `H¹` norm.  The paper (§2.1, display after `eq:sectorial-estimate-b`) states the bound in
the form `|im 𝔩_w(b,b)| ≤ re 𝔩_w(b,b) + C‖b‖₂²`; see the module docstring. -/
theorem horizontalWeakForm_abs_im_le (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) :
    |(horizontalWeakForm N w b b).im| ≤ horizontalImaginaryConstant N w * ‖b‖ ^ 2 := by
  have hcore := imaginary_core (abs_im_horizontalWeakForm_self_le N w b)
    (norm_horizontalStretchTransport_self_le w b)
    (norm_horizontalAxialForm_apply_le N w b b) (norm_nonneg w)
  simp only [horizontalImaginaryConstant, norm_sq_eq_gradientNormSq_add,
    horizontalGradientNormSq]
  linarith [hcore]

/-! ## The shifted form is closed and sectorial -/

/-- `𝔩_w` shifted by a real multiple of the `L²` mass form. -/
def horizontalShiftedWeakForm (N : ℝ) (w : WholePlaneC3LInf) (alpha : ℝ) :
    ComplexForm WholePlaneC2H1 :=
  horizontalWeakForm N w + (alpha : ℂ) • horizontalMassForm

/-- Evaluation of the shifted form. -/
theorem horizontalShiftedWeakForm_apply (N : ℝ) (w : WholePlaneC3LInf) (alpha : ℝ)
    (b phi : WholePlaneC2H1) :
    horizontalShiftedWeakForm N w alpha b phi =
      horizontalWeakForm N w b phi +
        (alpha : ℂ) * inner ℂ (wholePlaneH1Embedding C2 phi)
          (wholePlaneH1Embedding C2 b) :=
  rfl

/-- Real part of the shifted form on the diagonal. -/
theorem horizontalShiftedWeakForm_self_re (N : ℝ) (w : WholePlaneC3LInf) (alpha : ℝ)
    (b : WholePlaneC2H1) :
    (horizontalShiftedWeakForm N w alpha b b).re =
      (horizontalWeakForm N w b b).re + alpha * ‖wholePlaneH1Embedding C2 b‖ ^ 2 := by
  simp only [horizontalShiftedWeakForm_apply, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, inner_self_re, inner_self_im]
  ring

/-- The real mass shift does not change the imaginary part on the diagonal. -/
theorem horizontalShiftedWeakForm_self_im (N : ℝ) (w : WholePlaneC3LInf) (alpha : ℝ)
    (b : WholePlaneC2H1) :
    (horizontalShiftedWeakForm N w alpha b b).im = (horizontalWeakForm N w b b).im := by
  simp only [horizontalShiftedWeakForm_apply, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, inner_self_re, inner_self_im]
  ring

/-- The real shift making the form of `eq:jump-sectorial-form` coercive. -/
def horizontalGardingShift (N : ℝ) (w : WholePlaneC3LInf) : ℝ :=
  horizontalGardingConstant N w + 1 / 2

/-- After the Gårding shift the form is coercive on `H¹` with constant `1/2`; this is the
statement that `𝔩_w` is closed and bounded below (§2.1 of the paper). -/
theorem horizontalShiftedWeakForm_hasComplexCoercivityConstant (N : ℝ)
    (w : WholePlaneC3LInf) :
    HasComplexCoercivityConstant
      (horizontalShiftedWeakForm N w (horizontalGardingShift N w)) (1 / 2) := by
  refine ⟨by norm_num, ?_⟩
  intro b
  have hg := horizontalWeakForm_garding N w b
  have hn := norm_sq_eq_gradientNormSq_add b
  have hsq : ‖b‖ ^ 2 = ‖b‖ * ‖b‖ := pow_two ‖b‖
  rw [horizontalShiftedWeakForm_self_re, horizontalGardingShift]
  linarith

/-- Sectoriality: after the Gårding shift the imaginary part of the form is controlled by a
fixed multiple of its real part (§2.1 of the paper, where the multiple is `1` after a
larger shift). -/
theorem horizontalShiftedWeakForm_sectorial (N : ℝ) (w : WholePlaneC3LInf)
    (b : WholePlaneC2H1) :
    |(horizontalShiftedWeakForm N w (horizontalGardingShift N w) b b).im| ≤
      2 * horizontalImaginaryConstant N w *
        (horizontalShiftedWeakForm N w (horizontalGardingShift N w) b b).re := by
  have hcoer := (horizontalShiftedWeakForm_hasComplexCoercivityConstant N w).lower b
  have him := horizontalWeakForm_abs_im_le N w b
  have hC := horizontalImaginaryConstant_nonneg N w
  have h2 : horizontalImaginaryConstant N w * ‖b‖ ^ 2 ≤
      2 * horizontalImaginaryConstant N w *
        (horizontalShiftedWeakForm N w (horizontalGardingShift N w) b b).re := by
    have hmul := mul_le_mul_of_nonneg_left hcoer
      (by linarith : (0 : ℝ) ≤ 2 * horizontalImaginaryConstant N w)
    calc
      horizontalImaginaryConstant N w * ‖b‖ ^ 2
          = 2 * horizontalImaginaryConstant N w * (1 / 2 * ‖b‖ * ‖b‖) := by ring
      _ ≤ 2 * horizontalImaginaryConstant N w *
            (horizontalShiftedWeakForm N w (horizontalGardingShift N w) b b).re := hmul
  rw [horizontalShiftedWeakForm_self_im]
  linarith

end HorizontalWeakForm

end

end FastDynamo

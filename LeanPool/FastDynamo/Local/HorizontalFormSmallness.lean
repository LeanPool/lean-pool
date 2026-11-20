/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.HorizontalFormDelta
public import LeanPool.FastDynamo.Local.HorizontalFormPerturbation

/-!
# `eq:form-small`: the velocity and diffusivity form perturbation bound

This module completes the estimate

`‖𝔸_{h,δ}(z) - 𝔸_{0,1}(z)‖_{V→V*} ≤ C₁h^{1/4} + C₂|δ-1|`

of the proof of `prop:local-seed`.  The four velocity terms of
`eq:jump-sectorial-form` are bounded one by one with the Hölder exponents `(4,4,2)` and the
`H¹(ℝ²) ↪ L⁴(ℝ²)` embedding, using the infrastructure of
`Local/HorizontalFormPerturbation.lean`; the diffusion term is bounded directly on `V × V` by
`Local/HorizontalFormDelta.lean`.  The concluding statements are stated at the operator norm
`complexFormOpNorm` and are independent of the spectral parameter `z`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HorizontalWeakForm

open HorizontalMode PonomarenkoFreeOmegaInterface

/-! ## The four velocity terms of `eq:form-small` -/

section Terms

variable {w w' : WholePlaneC3LInf} {d : WholePlaneC3L4}

/-- The transport term `⟨w_⊥·∇_⊥b, φ⟩` is `L⁴`-form-small.  The derivative sits on `b`, so the
coefficient is moved onto the test function and the pairing is `L⁴ × L⁴ × L²`. -/
theorem norm_horizontalTransportForm_sub_apply_le
    (hd : (d : WholePlane → C3) =ᵐ[volume]
      fun y => (w : WholePlane → C3) y - (w' : WholePlane → C3) y)
    (hreal : ∀ᵐ y ∂volume, ∀ i : Fin 3, ((d : WholePlane → C3) y i).im = 0)
    (b phi : WholePlaneC2H1) :
    ‖horizontalTransportForm w b phi - horizontalTransportForm w' b phi‖ ≤
      2 * wholePlaneC2H1L4Bound * (‖d‖ * ‖b‖ * ‖phi‖) := by
  have hw : horizontalTransport w b = ∑ j : Fin 2, scalarVectorMulL2 (E := C2) volume
      (wholePlaneCoordLInf j.castSucc w) (wholePlaneH1FirstDerivative C2 j b) := by
    simp [horizontalTransport]
  have hw' : horizontalTransport w' b = ∑ j : Fin 2, scalarVectorMulL2 (E := C2) volume
      (wholePlaneCoordLInf j.castSucc w') (wholePlaneH1FirstDerivative C2 j b) := by
    simp [horizontalTransport]
  have hsub : horizontalTransport w b - horizontalTransport w' b =
      ∑ j : Fin 2, scalarVectorMulL2 (E := C2) volume
        (wholePlaneCoordLInf j.castSucc w - wholePlaneCoordLInf j.castSucc w')
        (wholePlaneH1FirstDerivative C2 j b) := by
    rw [hw, hw', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact scalarVectorMulL2_sub_coeff volume _ _ _
  have hterm : ∀ j : Fin 2,
      ‖inner ℂ (wholePlaneH1Embedding C2 phi)
          (scalarVectorMulL2 (E := C2) volume
            (wholePlaneCoordLInf j.castSucc w - wholePlaneCoordLInf j.castSucc w')
            (wholePlaneH1FirstDerivative C2 j b))‖ ≤
        wholePlaneC2H1L4Bound * (‖d‖ * ‖b‖ * ‖phi‖) := by
    intro j
    rw [inner_scalarVectorMulL2_swap volume _ (coordLInf_sub_im hd hreal j.castSucc)]
    refine (norm_inner_le_norm _ _).trans ?_
    have hleft : ‖scalarVectorMulL2 (E := C2) volume
        (wholePlaneCoordLInf j.castSucc w - wholePlaneCoordLInf j.castSucc w')
        (wholePlaneH1Embedding C2 phi)‖ ≤ ‖d‖ * (wholePlaneC2H1L4Bound * ‖phi‖) := by
      refine (norm_scalarVectorMulL2_coordLInf_sub_le hd j.castSucc _
        (wholePlaneC2H1ToL4 phi) (wholePlaneC2H1ToL4_coe_ae phi)).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_wholePlaneC2H1ToL4_le phi) (norm_nonneg d)
    have hright : ‖wholePlaneH1FirstDerivative C2 j b‖ ≤ ‖b‖ :=
      norm_wholePlaneH1FirstDerivative_le C2 b j
    calc
      ‖scalarVectorMulL2 (E := C2) volume
            (wholePlaneCoordLInf j.castSucc w - wholePlaneCoordLInf j.castSucc w')
            (wholePlaneH1Embedding C2 phi)‖ * ‖wholePlaneH1FirstDerivative C2 j b‖ ≤
          (‖d‖ * (wholePlaneC2H1L4Bound * ‖phi‖)) * ‖b‖ := by
        exact mul_le_mul hleft hright (norm_nonneg _)
          (mul_nonneg (norm_nonneg d)
            (mul_nonneg wholePlaneC2H1L4Bound_nonneg (norm_nonneg phi)))
      _ = wholePlaneC2H1L4Bound * (‖d‖ * ‖b‖ * ‖phi‖) := by ring
  simp only [horizontalTransportForm_apply, ← inner_sub_right, hsub, inner_sum]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hterm j).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The axial term `iN⟨w₃b, φ⟩` is `L⁴`-form-small: the coefficient multiplies the value of
`b`, whose `L⁴` representative is supplied by the embedding. -/
theorem norm_horizontalAxialForm_sub_apply_le (N : ℝ)
    (hd : (d : WholePlane → C3) =ᵐ[volume]
      fun y => (w : WholePlane → C3) y - (w' : WholePlane → C3) y)
    (b phi : WholePlaneC2H1) :
    ‖horizontalAxialForm N w b phi - horizontalAxialForm N w' b phi‖ ≤
      |N| * wholePlaneC2H1L4Bound * (‖d‖ * ‖b‖ * ‖phi‖) := by
  have hsub : scalarVectorMulL2 (E := C2) volume (wholePlaneCoordLInf 2 w)
        (wholePlaneH1Embedding C2 b) -
      scalarVectorMulL2 (E := C2) volume (wholePlaneCoordLInf 2 w')
        (wholePlaneH1Embedding C2 b) =
      scalarVectorMulL2 (E := C2) volume
        (wholePlaneCoordLInf 2 w - wholePlaneCoordLInf 2 w')
        (wholePlaneH1Embedding C2 b) := by
    exact scalarVectorMulL2_sub_coeff volume _ _ _
  have hsplit : horizontalAxialForm N w b phi - horizontalAxialForm N w' b phi =
      Complex.I * (N : ℂ) * inner ℂ (wholePlaneH1Embedding C2 phi)
        (scalarVectorMulL2 (E := C2) volume
          (wholePlaneCoordLInf 2 w - wholePlaneCoordLInf 2 w')
          (wholePlaneH1Embedding C2 b)) := by
    simp only [horizontalAxialForm_apply, ← hsub, inner_sub_right]
    ring
  have hconst : ‖Complex.I * (N : ℂ)‖ = |N| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hinner : ‖inner ℂ (wholePlaneH1Embedding C2 phi)
      (scalarVectorMulL2 (E := C2) volume
        (wholePlaneCoordLInf 2 w - wholePlaneCoordLInf 2 w')
        (wholePlaneH1Embedding C2 b))‖ ≤
      wholePlaneC2H1L4Bound * (‖d‖ * ‖b‖ * ‖phi‖) := by
    refine (norm_inner_le_norm _ _).trans ?_
    have hleft : ‖wholePlaneH1Embedding C2 phi‖ ≤ ‖phi‖ :=
      norm_wholePlaneH1Embedding_le C2 phi
    have hright : ‖scalarVectorMulL2 (E := C2) volume
        (wholePlaneCoordLInf 2 w - wholePlaneCoordLInf 2 w')
        (wholePlaneH1Embedding C2 b)‖ ≤ ‖d‖ * (wholePlaneC2H1L4Bound * ‖b‖) := by
      refine (norm_scalarVectorMulL2_coordLInf_sub_le hd 2 _ (wholePlaneC2H1ToL4 b)
        (wholePlaneC2H1ToL4_coe_ae b)).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_wholePlaneC2H1ToL4_le b) (norm_nonneg d)
    calc
      ‖wholePlaneH1Embedding C2 phi‖ * ‖scalarVectorMulL2 (E := C2) volume
            (wholePlaneCoordLInf 2 w - wholePlaneCoordLInf 2 w')
            (wholePlaneH1Embedding C2 b)‖ ≤
          ‖phi‖ * (‖d‖ * (wholePlaneC2H1L4Bound * ‖b‖)) :=
        mul_le_mul hleft hright (norm_nonneg _) (norm_nonneg _)
      _ = wholePlaneC2H1L4Bound * (‖d‖ * ‖b‖ * ‖phi‖) := by ring
  rw [hsplit, norm_mul, hconst]
  calc
    |N| * ‖inner ℂ (wholePlaneH1Embedding C2 phi)
          (scalarVectorMulL2 (E := C2) volume
            (wholePlaneCoordLInf 2 w - wholePlaneCoordLInf 2 w')
            (wholePlaneH1Embedding C2 b))‖ ≤
        |N| * (wholePlaneC2H1L4Bound * (‖d‖ * ‖b‖ * ‖phi‖)) :=
      mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
    _ = |N| * wholePlaneC2H1L4Bound * (‖d‖ * ‖b‖ * ‖phi‖) := by ring

/-- The divergence half `∫ w_⊥(Div_⊥b)conj φ` of the stretching term is `L⁴`-form-small.  As in the
transport term the derivative sits on `b`, so the coefficient is moved onto `φ`. -/
theorem norm_horizontalStretchDivergenceForm_sub_apply_le
    (hd : (d : WholePlane → C3) =ᵐ[volume]
      fun y => (w : WholePlane → C3) y - (w' : WholePlane → C3) y)
    (hreal : ∀ᵐ y ∂volume, ∀ i : Fin 3, ((d : WholePlane → C3) y i).im = 0)
    (b phi : WholePlaneC2H1) :
    ‖horizontalStretchDivergenceForm w b phi - horizontalStretchDivergenceForm w' b phi‖ ≤
      4 * ‖wholePlaneScalarH1ToL4‖ * (‖d‖ * ‖b‖ * ‖phi‖) := by
  have hterm : ∀ j : Fin 2,
      ‖inner ℂ (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 phi))
            (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w)
              (horizontalDivergence b)) -
          inner ℂ (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 phi))
            (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w')
              (horizontalDivergence b))‖ ≤
        2 * ‖wholePlaneScalarH1ToL4‖ * (‖d‖ * ‖b‖ * ‖phi‖) := by
    intro j
    have hsub : scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w)
          (horizontalDivergence b) -
        scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w')
          (horizontalDivergence b) =
        scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneCoordLInf j.castSucc w - wholePlaneCoordLInf j.castSucc w')
          (horizontalDivergence b) := by
      exact scalarVectorMulL2_sub_coeff volume _ _ _
    rw [← inner_sub_right, hsub,
      inner_scalarVectorMulL2_swap volume _ (coordLInf_sub_im hd hreal j.castSucc)]
    refine (norm_inner_le_norm _ _).trans ?_
    have hleft : ‖scalarVectorMulL2 (E := ℂ) volume
        (wholePlaneCoordLInf j.castSucc w - wholePlaneCoordLInf j.castSucc w')
        (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 phi))‖ ≤
        ‖d‖ * (‖wholePlaneScalarH1ToL4‖ * ‖phi‖) := by
      refine (norm_scalarVectorMulL2_coordLInf_sub_le hd j.castSucc _
        (horizontalComponentL4 j phi) (horizontalComponentL4_coe_ae j phi)).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_horizontalComponentL4_le j phi) (norm_nonneg d)
    calc
      ‖scalarVectorMulL2 (E := ℂ) volume
            (wholePlaneCoordLInf j.castSucc w - wholePlaneCoordLInf j.castSucc w')
            (wholePlaneC2CoordL2 j (wholePlaneH1Embedding C2 phi))‖ *
          ‖horizontalDivergence b‖ ≤
          (‖d‖ * (‖wholePlaneScalarH1ToL4‖ * ‖phi‖)) * (2 * ‖b‖) :=
        mul_le_mul hleft (norm_horizontalDivergence_le_two b) (norm_nonneg _) (by positivity)
      _ = 2 * ‖wholePlaneScalarH1ToL4‖ * (‖d‖ * ‖b‖ * ‖phi‖) := by ring
  simp only [horizontalStretchDivergenceForm_apply, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hterm j).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The gradient half `∫ w_⊥(b·∇_⊥)conj φ` of the stretching term is `L⁴`-form-small.  Here the
derivative sits on the test function, so the coefficient multiplies the value of `b`. -/
theorem norm_horizontalStretchGradientForm_sub_apply_le
    (hd : (d : WholePlane → C3) =ᵐ[volume]
      fun y => (w : WholePlane → C3) y - (w' : WholePlane → C3) y)
    (b phi : WholePlaneC2H1) :
    ‖horizontalStretchGradientForm w b phi - horizontalStretchGradientForm w' b phi‖ ≤
      4 * ‖wholePlaneScalarH1ToL4‖ * (‖d‖ * ‖b‖ * ‖phi‖) := by
  have hterm : ∀ j k : Fin 2,
      ‖inner ℂ (wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 k phi))
            (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w)
              (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b))) -
          inner ℂ (wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 k phi))
            (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w')
              (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b)))‖ ≤
        ‖wholePlaneScalarH1ToL4‖ * (‖d‖ * ‖b‖ * ‖phi‖) := by
    intro j k
    have hsub : scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w)
          (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b)) -
        scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w')
          (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b)) =
        scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneCoordLInf j.castSucc w - wholePlaneCoordLInf j.castSucc w')
          (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b)) := by
      exact scalarVectorMulL2_sub_coeff volume _ _ _
    rw [← inner_sub_right, hsub]
    refine (norm_inner_le_norm _ _).trans ?_
    have hleft : ‖wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 k phi)‖ ≤ ‖phi‖ :=
      (norm_wholePlaneC2CoordL2_apply_le j _).trans
        (norm_wholePlaneH1FirstDerivative_le C2 phi k)
    have hright : ‖scalarVectorMulL2 (E := ℂ) volume
        (wholePlaneCoordLInf j.castSucc w - wholePlaneCoordLInf j.castSucc w')
        (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b))‖ ≤
        ‖d‖ * (‖wholePlaneScalarH1ToL4‖ * ‖b‖) := by
      refine (norm_scalarVectorMulL2_coordLInf_sub_le hd j.castSucc _
        (horizontalComponentL4 k b) (horizontalComponentL4_coe_ae k b)).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_horizontalComponentL4_le k b) (norm_nonneg d)
    calc
      ‖wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 k phi)‖ *
          ‖scalarVectorMulL2 (E := ℂ) volume
            (wholePlaneCoordLInf j.castSucc w - wholePlaneCoordLInf j.castSucc w')
            (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b))‖ ≤
          ‖phi‖ * (‖d‖ * (‖wholePlaneScalarH1ToL4‖ * ‖b‖)) :=
        mul_le_mul hleft hright (norm_nonneg _) (norm_nonneg _)
      _ = ‖wholePlaneScalarH1ToL4‖ * (‖d‖ * ‖b‖ * ‖phi‖) := by ring
  simp only [horizontalStretchGradientForm_apply, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hrow : ∀ j : Fin 2,
      ‖∑ k : Fin 2, (inner ℂ (wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 k phi))
            (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w)
              (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b))) -
          inner ℂ (wholePlaneC2CoordL2 j (wholePlaneH1FirstDerivative C2 k phi))
            (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w')
              (wholePlaneC2CoordL2 k (wholePlaneH1Embedding C2 b))))‖ ≤
        2 * ‖wholePlaneScalarH1ToL4‖ * (‖d‖ * ‖b‖ * ‖phi‖) := by
    intro j
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hterm j k).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  refine (Finset.sum_le_sum fun j _ => hrow j).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-! ## The velocity half of `eq:form-small` -/

/-- The explicit constant of the velocity half of `eq:form-small`.  It depends only on `N`, on
the two-component `H¹(ℝ²;ℂ²) ↪ L⁴(ℝ²;ℂ²)` constant and on the scalar one, and in particular
neither on `z` nor on the two velocities. -/
def horizontalVelocityPerturbationConstant (N : ℝ) : ℝ :=
  (2 + |N|) * wholePlaneC2H1L4Bound + 8 * ‖wholePlaneScalarH1ToL4‖

/-- The velocity-perturbation constant is nonnegative. -/
theorem horizontalVelocityPerturbationConstant_nonneg (N : ℝ) :
    0 ≤ horizontalVelocityPerturbationConstant N := by
  have hK := wholePlaneC2H1L4Bound_nonneg
  have hK4 := ContinuousLinearMap.opNorm_nonneg wholePlaneScalarH1ToL4
  have hN := abs_nonneg N
  unfold horizontalVelocityPerturbationConstant
  nlinarith

/-- Four-term triangle inequality. -/
private theorem norm_add_four_le (z1 z2 z3 z4 : ℂ) :
    ‖z1 + z2 + z3 + z4‖ ≤ ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ := by
  have h12 := norm_add_le z1 z2
  have h123 := norm_add_le (z1 + z2) z3
  have h1234 := norm_add_le (z1 + z2 + z3) z4
  linarith

/-- **The velocity half of `eq:form-small`**: the four velocity terms of
`eq:jump-sectorial-form` differ by at most `C‖v - v'‖_{L⁴}‖b‖_{H¹}‖φ‖_{H¹}`. -/
theorem norm_horizontalVelocityForm_sub_apply_le (N : ℝ)
    (hd : (d : WholePlane → C3) =ᵐ[volume]
      fun y => (w : WholePlane → C3) y - (w' : WholePlane → C3) y)
    (hreal : ∀ᵐ y ∂volume, ∀ i : Fin 3, ((d : WholePlane → C3) y i).im = 0)
    (b phi : WholePlaneC2H1) :
    ‖horizontalVelocityForm N w b phi - horizontalVelocityForm N w' b phi‖ ≤
      horizontalVelocityPerturbationConstant N * ‖d‖ * ‖b‖ * ‖phi‖ := by
  have hA := norm_horizontalTransportForm_sub_apply_le hd hreal b phi
  have hB := norm_horizontalAxialForm_sub_apply_le N hd b phi
  have hC := norm_horizontalStretchDivergenceForm_sub_apply_le hd hreal b phi
  have hD := norm_horizontalStretchGradientForm_sub_apply_le hd b phi
  have hsplit : horizontalVelocityForm N w b phi - horizontalVelocityForm N w' b phi =
      (horizontalTransportForm w b phi - horizontalTransportForm w' b phi) +
        (horizontalAxialForm N w b phi - horizontalAxialForm N w' b phi) +
        (horizontalStretchDivergenceForm w b phi -
          horizontalStretchDivergenceForm w' b phi) +
        (horizontalStretchGradientForm w b phi -
          horizontalStretchGradientForm w' b phi) := by
    simp only [horizontalVelocityForm, add_apply]
    ring
  have hconst : horizontalVelocityPerturbationConstant N * ‖d‖ * ‖b‖ * ‖phi‖ =
      2 * wholePlaneC2H1L4Bound * (‖d‖ * ‖b‖ * ‖phi‖) +
        |N| * wholePlaneC2H1L4Bound * (‖d‖ * ‖b‖ * ‖phi‖) +
        4 * ‖wholePlaneScalarH1ToL4‖ * (‖d‖ * ‖b‖ * ‖phi‖) +
        4 * ‖wholePlaneScalarH1ToL4‖ * (‖d‖ * ‖b‖ * ‖phi‖) := by
    unfold horizontalVelocityPerturbationConstant
    ring
  have htri : ‖horizontalVelocityForm N w b phi - horizontalVelocityForm N w' b phi‖ ≤
      ‖horizontalTransportForm w b phi - horizontalTransportForm w' b phi‖ +
        ‖horizontalAxialForm N w b phi - horizontalAxialForm N w' b phi‖ +
        ‖horizontalStretchDivergenceForm w b phi -
          horizontalStretchDivergenceForm w' b phi‖ +
        ‖horizontalStretchGradientForm w b phi -
          horizontalStretchGradientForm w' b phi‖ := by
    refine le_trans (le_of_eq (congrArg norm hsplit)) ?_
    exact norm_add_four_le _ _ _ _
  linarith

/-- The velocity half of `eq:form-small` at the `V → V*` operator norm. -/
theorem complexFormOpNorm_horizontalVelocityForm_sub_le (N : ℝ)
    (hd : (d : WholePlane → C3) =ᵐ[volume]
      fun y => (w : WholePlane → C3) y - (w' : WholePlane → C3) y)
    (hreal : ∀ᵐ y ∂volume, ∀ i : Fin 3, ((d : WholePlane → C3) y i).im = 0) :
    complexFormOpNorm (horizontalVelocityForm N w - horizontalVelocityForm N w') ≤
      horizontalVelocityPerturbationConstant N * ‖d‖ := by
  refine complexFormOpNorm_le_of_apply_le _
    (mul_nonneg (horizontalVelocityPerturbationConstant_nonneg N) (norm_nonneg d))
    fun b phi => ?_
  simpa only [sub_apply] using norm_horizontalVelocityForm_sub_apply_le N hd hreal b phi

/-! ## `eq:form-small` -/

/-- **`eq:form-small`** at the `V → V*` operator norm,
with a constant independent of the spectral parameter `z`. -/
theorem complexFormOpNorm_horizontalPencilFormDelta_sub_le (N delta delta' : ℝ)
    (hd : (d : WholePlane → C3) =ᵐ[volume]
      fun y => (w : WholePlane → C3) y - (w' : WholePlane → C3) y)
    (hreal : ∀ᵐ y ∂volume, ∀ i : Fin 3, ((d : WholePlane → C3) y i).im = 0) (z : ℂ) :
    complexFormOpNorm (horizontalPencilFormDelta N delta w z -
        horizontalPencilFormDelta N delta' w' z) ≤
      horizontalVelocityPerturbationConstant N * ‖d‖ + |delta - delta'| * (2 + N ^ 2) := by
  refine le_trans (le_of_eq (congrArg complexFormOpNorm
    (horizontalPencilFormDelta_sub N delta delta' w w' z))) ?_
  refine (complexFormOpNorm_add_le _ _).trans ?_
  exact add_le_add (complexFormOpNorm_horizontalVelocityForm_sub_le N hd hreal)
    (complexFormOpNorm_smul_horizontalDiffusionForm_le N delta delta')

end Terms

/-! ## `eq:form-small` for the smoothed family -/

/-- **The estimate `eq:form-small` of the proof of `prop:local-seed`**:

`‖𝔸_{h,δ}(z) - 𝔸_{0,1}(z)‖_{V→V*} ≤ C₁h^{1/4} + C₂|δ-1|`,   `C₂ = 2 + N²`,

uniformly in the smoothing width `h`, the diffusivity `δ` and the spectral parameter `z`. -/
theorem exists_complexFormOpNorm_horizontalSmoothedPencil_sub_le (N Omega U : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : PonomarenkoSmoothingWidth) (delta : ℝ) (z : ℂ),
      complexFormOpNorm
          (horizontalPencilFormDelta N delta (horizontalSmoothedVelocityLInf Omega U h) z -
            horizontalPencilFormDelta N 1 (horizontalJumpVelocityLInf Omega U) z) ≤
        C * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2) := by
  obtain ⟨C0, hC0, hrate⟩ := exists_norm_horizontalSmoothingErrorL4_le Omega U
  refine ⟨horizontalVelocityPerturbationConstant N * C0,
    mul_nonneg (horizontalVelocityPerturbationConstant_nonneg N) hC0, fun h delta z => ?_⟩
  refine (complexFormOpNorm_horizontalPencilFormDelta_sub_le N delta 1
    (d := horizontalSmoothingErrorL4 Omega U h)
    (horizontalSmoothingErrorL4_coe_ae_sub Omega U h)
    (horizontalSmoothingErrorL4_im Omega U h) z).trans ?_
  have hmul : horizontalVelocityPerturbationConstant N *
      ‖horizontalSmoothingErrorL4 Omega U h‖ ≤
      horizontalVelocityPerturbationConstant N * (C0 * (h : ℝ) ^ (1 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_left (hrate h) (horizontalVelocityPerturbationConstant_nonneg N)
  have heq : horizontalVelocityPerturbationConstant N * C0 * (h : ℝ) ^ (1 / 4 : ℝ) =
      horizontalVelocityPerturbationConstant N * (C0 * (h : ℝ) ^ (1 / 4 : ℝ)) := by ring
  linarith

/-- `eq:form-small` for the certified mode velocity, whose axial speed is the paper's
`U = -Ω/N`. -/
theorem exists_complexFormOpNorm_horizontalModePencil_sub_le (N Omega : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : PonomarenkoSmoothingWidth) (delta : ℝ) (z : ℂ),
      complexFormOpNorm
          (horizontalPencilFormDelta N delta (horizontalSmoothedModeVelocity N Omega h) z -
            horizontalPencilFormDelta N 1 (horizontalModeVelocity N Omega) z) ≤
        C * (h : ℝ) ^ (1 / 4 : ℝ) + |delta - 1| * (2 + N ^ 2) :=
  exists_complexFormOpNorm_horizontalSmoothedPencil_sub_le N Omega (jumpAxialSpeed N Omega)

end HorizontalWeakForm

end

end FastDynamo

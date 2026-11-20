/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalWeakForm
public import LeanPool.FastDynamo.Operator.ComplexFormAntiDual
public import LeanPool.FastDynamo.Operator.CompactOperatorSum

/-!
# The horizontal operator `A_w` associated with `𝔩_w`

Following §2.1 of the paper we denote by `-A_w` the operator on
`L²(ℝ²;ℂ²)` associated with the closed sectorial form `𝔩_w` of `eq:jump-sectorial-form`
(Kato, Theorem VI.2.1).  The generic construction is
`FastDynamo/Operator/AssociatedForm.lean`; the only inputs are that the form-domain
embedding `H¹(ℝ²;ℂ²) → L²(ℝ²;ℂ²)` is injective with dense range.

The paper's characterisation

`b ∈ D(A_w)` and `A_w b = f` iff `b ∈ H¹` and `𝔩_w(b,φ) = -⟨f,φ⟩` for every `φ ∈ H¹`

is `horizontalFormOperator_exists_iff` below.

The second half of the file sets up the shifted form operator of §2.3 of the paper,

`𝔸_w(z) = F_z + K_w : V → V*`,   `F_z = z - (Δ_⊥ - N²)`,   `V = H¹(ℝ²;ℂ²)`,

and proves that `F_z` is an isomorphism from `V` onto its antidual `V*` for `re z > 0`.
The paper (where `N = 2π`, so `N² = 4π²`) obtains this from the Fourier multiplier
`(z + |ξ|² + N²)⁻¹`; here it is
obtained from the exact identity `re F_z(b,b) = ‖∇_⊥b‖² + (N² + re z)‖b‖²`, which makes `F_z`
coercive, followed by complex Lax-Milgram (`FastDynamo/Analysis/ComplexForm.lean`).  The two
routes give the same operator, the form being determined by its values.

Finally the velocity part `K_w` is split into the two halves that carry no transverse
derivative on the input, and those are shown to be compact whenever `w` vanishes outside a
disc.  The remaining two halves require the adjoint of a compact operator; they are treated
in `FastDynamo/Local/HorizontalFormCompactness.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HorizontalWeakForm

/-! ## The associated operator -/

/-- Maximal graph domain of the negative operator associated with `𝔩_w`. -/
abbrev HorizontalFormDomain (N : ℝ) (w : WholePlaneC3LInf) :=
  AssociatedFormProdDomain (wholePlaneH1Embedding C2) (horizontalWeakForm N w)

/-- The operator `A_w` of `eq:horizontal-induction`, realised as the domain-aware operator
whose negative is associated with `𝔩_w` (§2.1 of the paper). -/
def horizontalFormOperator (N : ℝ) (w : WholePlaneC3LInf) :
    DomainOperator WholePlaneC2L2 (HorizontalFormDomain N w) :=
  associatedFormProdOperator (wholePlaneH1Embedding C2)
    (wholePlaneC2H1Embedding_injective) denseRange_wholePlaneC2H1Embedding
    (horizontalWeakForm N w)

/-- The domain embedding of `A_w` is the physical `H¹ → L²` map of the first graph
coordinate. -/
@[simp] theorem horizontalFormOperator_embedding_apply (N : ℝ) (w : WholePlaneC3LInf)
    (u : HorizontalFormDomain N w) :
    (horizontalFormOperator N w).embedding u = wholePlaneH1Embedding C2 u.1.1 :=
  rfl

/-- The action of `A_w` is the negative of the stored pivot vector. -/
@[simp] theorem horizontalFormOperator_op_apply (N : ℝ) (w : WholePlaneC3LInf)
    (u : HorizontalFormDomain N w) :
    (horizontalFormOperator N w).op u = -u.1.2 :=
  rfl

/-- The weak identity stored by every element of the graph domain. -/
theorem horizontalFormDomain_relation (N : ℝ) (w : WholePlaneC3LInf)
    (u : HorizontalFormDomain N w) (phi : WholePlaneC2H1) :
    horizontalWeakForm N w u.1.1 phi =
      inner ℂ (wholePlaneH1Embedding C2 phi) u.1.2 :=
  associatedFormProdDomain_relation_apply (wholePlaneH1Embedding C2)
    (horizontalWeakForm N w) u phi

/-- The paper's domain characterisation (end of §2.1):
`b ∈ D(A_w)` with `A_w b = f` exactly when `b ∈ H¹` and `𝔩_w(b,φ) = -⟨f,φ⟩` for all
`φ ∈ H¹`.  The pairing `⟨f,φ⟩`, linear in `f`, is `inner ℂ (j φ) f` in Lean. -/
theorem horizontalFormOperator_exists_iff (N : ℝ) (w : WholePlaneC3LInf)
    (b : WholePlaneC2H1) (f : WholePlaneC2L2) :
    (∃ u : HorizontalFormDomain N w,
        u.1.1 = b ∧ (horizontalFormOperator N w).op u = f) ↔
      ∀ phi : WholePlaneC2H1,
        horizontalWeakForm N w b phi =
          -inner ℂ (wholePlaneH1Embedding C2 phi) f := by
  constructor
  · rintro ⟨u, rfl, hf⟩
    intro phi
    have hrel := horizontalFormDomain_relation N w u phi
    have hsnd : u.1.2 = -f := by
      have : -u.1.2 = f := hf
      linear_combination (norm := module) -this
    rw [hrel, hsnd, inner_neg_right]
  · intro h
    refine ⟨⟨(b, -f), ?_⟩, rfl, ?_⟩
    · rw [mem_associatedFormProdDomain_iff_forall]
      intro phi
      rw [h phi, inner_neg_right]
    · change -(-f) = f
      rw [neg_neg]

/-- An eigenpair of `A_w` in the sense of `DomainOperator.IsEigenpair`, written out through
the weak identity. -/
theorem horizontalFormOperator_isEigenpair_iff (N : ℝ) (w : WholePlaneC3LInf)
    (lambda : ℂ) (u : HorizontalFormDomain N w) :
    (horizontalFormOperator N w).IsEigenpair lambda u ↔
      wholePlaneH1Embedding C2 u.1.1 ≠ 0 ∧
        -u.1.2 = lambda • wholePlaneH1Embedding C2 u.1.1 :=
  Iff.rfl

/-! ## The shifted form operator `𝔸_w(z) = F_z + K_w` -/

/-- The free horizontal form `F_z = z - (Δ_⊥ - N²)` of §2.3 of the paper, written weakly on
`H¹(ℝ²;ℂ²)`. -/
def freeHorizontalForm (N : ℝ) (z : ℂ) : ComplexForm WholePlaneC2H1 :=
  horizontalDirichletForm + ((N : ℂ) ^ 2 + z) • horizontalMassForm

/-- The velocity part `K_w` of the shifted form operator: the four terms of
`eq:jump-sectorial-form` that carry the velocity. -/
def horizontalVelocityForm (N : ℝ) (w : WholePlaneC3LInf) : ComplexForm WholePlaneC2H1 :=
  horizontalTransportForm w + horizontalAxialForm N w +
    horizontalStretchDivergenceForm w + horizontalStretchGradientForm w

/-- The shifted form operator `𝔸_w(z) = F_z + K_w : V → V*`. -/
def horizontalPencilForm (N : ℝ) (w : WholePlaneC3LInf) (z : ℂ) :
    ComplexForm WholePlaneC2H1 :=
  freeHorizontalForm N z + horizontalVelocityForm N w

/-- `𝔸_w(z)` is the weak form of the pencil `z - A_w`: on every pair it is `𝔩_w` plus the
`L²` mass term `z⟨b,φ⟩`. -/
theorem horizontalPencilForm_apply (N : ℝ) (w : WholePlaneC3LInf) (z : ℂ)
    (b phi : WholePlaneC2H1) :
    horizontalPencilForm N w z b phi =
      horizontalWeakForm N w b phi +
        z * inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneH1Embedding C2 b) := by
  have hL : horizontalPencilForm N w z b phi =
      horizontalDirichletForm b phi +
          ((N : ℂ) ^ 2 + z) *
            inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneH1Embedding C2 b) +
        (horizontalTransportForm w b phi + horizontalAxialForm N w b phi +
          horizontalStretchDivergenceForm w b phi +
          horizontalStretchGradientForm w b phi) := rfl
  have hR : horizontalWeakForm N w b phi =
      horizontalDirichletForm b phi +
            (N : ℂ) ^ 2 *
              inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneH1Embedding C2 b) +
          horizontalTransportForm w b phi + horizontalAxialForm N w b phi +
          horizontalStretchDivergenceForm w b phi +
        horizontalStretchGradientForm w b phi := rfl
  linear_combination hL - hR

/-- Evaluation of the free form. -/
theorem freeHorizontalForm_apply (N : ℝ) (z : ℂ) (b phi : WholePlaneC2H1) :
    freeHorizontalForm N z b phi =
      (∑ j : Fin 2, inner ℂ (wholePlaneH1FirstDerivative C2 j phi)
          (wholePlaneH1FirstDerivative C2 j b)) +
        ((N : ℂ) ^ 2 + z) *
          inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneH1Embedding C2 b) := by
  simp [freeHorizontalForm, horizontalDirichletForm_apply]

/-- The exact diagonal real part of the free form. -/
theorem freeHorizontalForm_self_re (N : ℝ) (z : ℂ) (b : WholePlaneC2H1) :
    (freeHorizontalForm N z b b).re =
      horizontalGradientNormSq b +
        (N ^ 2 + z.re) * ‖wholePlaneH1Embedding C2 b‖ ^ 2 := by
  simp only [freeHorizontalForm_apply, Fin.sum_univ_two, horizontalGradientNormSq,
    ← Complex.ofReal_pow, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    inner_self_re, inner_self_im]
  ring

/-- The transverse gradient norm is nonnegative. -/
theorem horizontalGradientNormSq_nonneg (b : WholePlaneC2H1) :
    0 ≤ horizontalGradientNormSq b := by
  unfold horizontalGradientNormSq
  positivity

/-- For `re z > 0` the free form is coercive on `H¹(ℝ²;ℂ²)` with constant `min 1 (re z)`.
This is the quantitative content of the paper's Fourier-multiplier argument in §2.3. -/
theorem freeHorizontalForm_hasComplexCoercivityConstant (N : ℝ) {z : ℂ} (hz : 0 < z.re) :
    HasComplexCoercivityConstant (freeHorizontalForm N z) (min 1 z.re) := by
  refine ⟨lt_min one_pos hz, ?_⟩
  intro b
  have hre := freeHorizontalForm_self_re N z b
  have hG := horizontalGradientNormSq_nonneg b
  have hm : (0 : ℝ) ≤ ‖wholePlaneH1Embedding C2 b‖ ^ 2 := sq_nonneg _
  have hN : (0 : ℝ) ≤ N ^ 2 := sq_nonneg N
  have hmin1 : min 1 z.re ≤ 1 := min_le_left _ _
  have hminz : min 1 z.re ≤ z.re := min_le_right _ _
  have h1 : min 1 z.re * ‖wholePlaneH1Embedding C2 b‖ ^ 2 ≤
      z.re * ‖wholePlaneH1Embedding C2 b‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hminz hm
  have h2 : min 1 z.re * horizontalGradientNormSq b ≤ 1 * horizontalGradientNormSq b :=
    mul_le_mul_of_nonneg_right hmin1 hG
  have h3 : (0 : ℝ) ≤ N ^ 2 * ‖wholePlaneH1Embedding C2 b‖ ^ 2 := mul_nonneg hN hm
  have hbb : ‖b‖ * ‖b‖ =
      ‖wholePlaneH1Embedding C2 b‖ ^ 2 + horizontalGradientNormSq b := by
    rw [← pow_two, norm_sq_eq_gradientNormSq_add]
  calc
    min 1 z.re * ‖b‖ * ‖b‖
        = min 1 z.re *
          (‖wholePlaneH1Embedding C2 b‖ ^ 2 + horizontalGradientNormSq b) := by
      rw [mul_assoc, hbb]
    _ ≤ (freeHorizontalForm N z b b).re := by linarith [hre, h1, h2, h3]

/-- For `re z > 0` the free form is an isomorphism from `V = H¹(ℝ²;ℂ²)` onto its antidual
`V* = H⁻¹(ℝ²;ℂ²)` (§2.3 of the paper). -/
def freeHorizontalFormEquiv (N : ℝ) {z : ℂ} (hz : 0 < z.re) :
    WholePlaneC2H1 ≃L[ℂ] ComplexAntiDual WholePlaneC2H1 :=
  (IsComplexCoercive.continuousLinearEquiv (freeHorizontalForm N z)
      (freeHorizontalForm_hasComplexCoercivityConstant N hz).isComplexCoercive).trans
    (complexToAntiDual (E := WholePlaneC2H1)).toContinuousLinearEquiv

/-- The isomorphism of the previous definition is the free form itself. -/
theorem freeHorizontalFormEquiv_apply (N : ℝ) {z : ℂ} (hz : 0 < z.re)
    (b : WholePlaneC2H1) :
    freeHorizontalFormEquiv N hz b = freeHorizontalForm N z b :=
  complexToAntiDual_complexFormOperator (freeHorizontalForm N z) b

/-- `F_z : V → V*` is bijective for `re z > 0`. -/
theorem freeHorizontalForm_bijective (N : ℝ) {z : ℂ} (hz : 0 < z.re) :
    Function.Bijective (freeHorizontalForm N z) := by
  have hfun : (freeHorizontalForm N z : WholePlaneC2H1 → ComplexAntiDual WholePlaneC2H1) =
      freeHorizontalFormEquiv N hz := by
    funext b
    exact (freeHorizontalFormEquiv_apply N hz b).symm
  rw [hfun]
  exact (freeHorizontalFormEquiv N hz).bijective

/-! ## Compactness of the zeroth-order half of `K_w`

The compactness paragraph of §2.3 splits `K_w` into the terms carrying a transverse
derivative on the test function, which factor through the compact restriction
`H¹(ℝ²) → L²(D)`, and the terms carrying a derivative on the input, which factor through the
adjoint compact map `L²(D) → H⁻¹(ℝ²)`, and treats the zeroth-order term separately.  Here the
first kind and the zeroth-order term are proved compact; the adjoint step is in
`FastDynamo/Local/HorizontalFormCompactness.lean`.
-/

/-- The axial term `iN⟨w₃b,φ⟩` is compact on `H¹` when `w₃` vanishes off a set of finite
measure: it factors through the local Rellich embedding. -/
theorem isCompactOperator_horizontalAxialForm_of_ae_zero_off
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (N : ℝ) (w : WholePlaneC3LInf)
    (hw : ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf 2 w x = 0) :
    IsCompactOperator (horizontalAxialForm N w) := by
  have hloc : IsCompactOperator (wholePlaneC2LocalizationH1 (wholePlaneCoordLInf 2 w)) :=
    isCompactOperator_wholePlaneC2LocalizationH1_of_ae_zero_off s hs hsm _ hw
  have h1 : IsCompactOperator
      ((associatedFormPivot (wholePlaneH1Embedding C2)).comp
        (wholePlaneC2LocalizationH1 (wholePlaneCoordLInf 2 w))) :=
    hloc.clm_comp (associatedFormPivot (wholePlaneH1Embedding C2))
  have heq : horizontalAxialForm N w =
      (Complex.I * (N : ℂ)) •
        ((associatedFormPivot (wholePlaneH1Embedding C2)).comp
          (wholePlaneC2LocalizationH1 (wholePlaneCoordLInf 2 w))) := rfl
  rw [heq]
  simpa using h1.smul (Complex.I * (N : ℂ))

/-- Each `(j,k)` term of the gradient half of the stretching form is compact for a supported
velocity coefficient. -/
private theorem isCompactOperator_stretchGradientTerm
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (w : WholePlaneC3LInf) (j k : Fin 2)
    (hw : ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0) :
    IsCompactOperator
      ((associatedFormPivot
          ((wholePlaneC2CoordL2 j).comp (wholePlaneH1FirstDerivative C2 k))).comp
        ((scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w)).comp
          ((wholePlaneC2CoordL2 k).comp (wholePlaneH1Embedding C2)))) := by
  have hscalar : IsCompactOperator
      (wholePlaneScalarLocalizationH1 (wholePlaneCoordLInf j.castSucc w)) :=
    isCompactOperator_wholePlaneScalarLocalizationH1_of_ae_zero_off s hs hsm _ hw
  have hinner : IsCompactOperator
      ((wholePlaneScalarLocalizationH1 (wholePlaneCoordLInf j.castSucc w)).comp
        (wholePlaneC2CoordH1 k)) :=
    hscalar.comp_clm (wholePlaneC2CoordH1 k)
  have heq : (scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w)).comp
        ((wholePlaneC2CoordL2 k).comp (wholePlaneH1Embedding C2)) =
      (wholePlaneScalarLocalizationH1 (wholePlaneCoordLInf j.castSucc w)).comp
        (wholePlaneC2CoordH1 k) := rfl
  rw [heq]
  exact hinner.clm_comp
    (associatedFormPivot ((wholePlaneC2CoordL2 j).comp (wholePlaneH1FirstDerivative C2 k)))

/-- The gradient half `∫ w_⊥·(b·∇_⊥)conj φ` of the stretching term is compact on `H¹` when the
horizontal velocity coordinates vanish off a set of finite measure. -/
theorem isCompactOperator_horizontalStretchGradientForm_of_ae_zero_off
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (w : WholePlaneC3LInf)
    (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0) :
    IsCompactOperator (horizontalStretchGradientForm w) := by
  have hsplit : horizontalStretchGradientForm w =
      ∑ j : Fin 2, ∑ k : Fin 2,
        (associatedFormPivot
            ((wholePlaneC2CoordL2 j).comp (wholePlaneH1FirstDerivative C2 k))).comp
          ((scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w)).comp
            ((wholePlaneC2CoordL2 k).comp (wholePlaneH1Embedding C2))) := rfl
  rw [hsplit]
  apply isCompactOperator_finsetSum
  intro j
  apply isCompactOperator_finsetSum
  intro k
  exact isCompactOperator_stretchGradientTerm s hs hsm w j k (hw j)

/-- The two halves of `K_w` that carry no transverse derivative on the input are compact for a
velocity supported in a set of finite measure. -/
theorem isCompactOperator_horizontalVelocityZeroOrder_of_ae_zero_off
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (N : ℝ) (w : WholePlaneC3LInf)
    (hw3 : ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf 2 w x = 0)
    (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0) :
    IsCompactOperator (horizontalAxialForm N w + horizontalStretchGradientForm w) := by
  have h1 := isCompactOperator_horizontalAxialForm_of_ae_zero_off s hs hsm N w hw3
  have h2 := isCompactOperator_horizontalStretchGradientForm_of_ae_zero_off s hs hsm w hw
  simpa using h1.add h2

end HorizontalWeakForm

end

end FastDynamo

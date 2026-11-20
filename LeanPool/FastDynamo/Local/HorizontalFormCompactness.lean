/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.HorizontalFormOperator
public import LeanPool.FastDynamo.Analysis.AnalyticOperatorHelpers
public import LeanPool.FastDynamo.Operator.ScalarCoefficientPivot
public import LeanPool.FastDynamo.Operator.CompactAdjoint
public import LeanPool.FastDynamo.Operator.AnalyticFredholmContinuation
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Constructions

/-!
# Compactness of the full lower-order form `K_w`, and the Fredholm factorisation of `𝔸_w(z)`

The compactness paragraph of §2.3 of the paper splits the velocity part

`K_w = ⟨w_⊥·∇_⊥b, φ⟩ + iN⟨w₃b, φ⟩ + ∫ w_⊥(Div_⊥b)conj φ + ∫ w_⊥(b·∇_⊥)conj φ : V → V*`

(the paper writes `2π` for `N`) into the terms carrying a transverse derivative on the
*test function*, which factor through the compact restriction `H¹(ℝ²) → L²(D)`, the terms
carrying a derivative on the *input*, which factor through the adjoint compact map
`L²(D) → H⁻¹(ℝ²)`, and the zeroth-order term.  Here the zeroth-order term `iN⟨w₃b, φ⟩` is
grouped with `∫ w_⊥(b·∇_⊥)conj φ` as the pair carrying no derivative on the input, whose
compactness `FastDynamo/Local/HorizontalFormOperator.lean` proves.  This module proves
compactness of the two terms carrying a derivative on the input, hence of `K_w`, using
Schauder's theorem `isCompactOperator_associatedFormPivot_of_compact` of
`FastDynamo/Operator/CompactAdjoint.lean`.

The mechanism is an exact rewriting, not an approximation: since `associatedFormPivot j` is
the pairing `f ↦ (φ ↦ ⟪j φ, f⟫)`, and multiplication by a bounded scalar coefficient `a` on
`L²` has multiplication by `star a` as its adjoint, one has

`(associatedFormPivot j) ∘ (a ·) = associatedFormPivot ((star a ·) ∘ j)`,

and the right-hand pivot embedding is exactly the compact localisation map of the local
Rellich theorem.  The derivative that remains on the input is then a *bounded* factor.

The second half assembles the factorisation of the shifted form operator of §2.3,

`𝔸_w(z) = F_z + K_w = F_z (1 - K(z))`,  `K(z) = -F_z⁻¹K_w`,

in the vocabulary of `FastDynamo/Operator/AnalyticFredholm.lean`: `K(z)` is a compact-valued
family, holomorphic in the operator norm on the open right half plane, whose
`AnalyticFredholm.compactPencil` is invertible exactly when `𝔸_w(z)` is an isomorphism
`V → V*`.  Holomorphy of `z ↦ F_z⁻¹` is cheap because `F_z` is *affine* in `z`: normalising by
the fixed isomorphism `F_1` turns it into the entire endomorphism family
`G_z = F_1⁻¹F_z = 1 + (z-1)F_1⁻¹M`, whose inverse is analytic on the invertible locus by
Mathlib's Neumann series (`AnalyticFredholm.analyticAt_inverse`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HorizontalWeakForm

/-! ## The two halves of `K_w` carrying a derivative on the input -/

/-- The transport form written with the velocity coefficient moved onto the test slot: each
summand is the anti-dual pivot of a *compact* localisation composed with the bounded weak
derivative. -/
theorem horizontalTransportForm_eq_sum (w : WholePlaneC3LInf) :
    horizontalTransportForm w =
      ∑ j : Fin 2, (associatedFormPivot
          (wholePlaneC2LocalizationH1 (star (wholePlaneCoordLInf j.castSucc w)))).comp
        (wholePlaneH1FirstDerivative C2 j) := by
  have hsplit : horizontalTransportForm w =
      ∑ j : Fin 2,
        ((associatedFormPivot (wholePlaneH1Embedding C2)).comp
            (scalarVectorMulL2 (E := C2) volume (wholePlaneCoordLInf j.castSucc w))).comp
          (wholePlaneH1FirstDerivative C2 j) := by
    refine ContinuousLinearMap.ext fun b => ?_
    simp only [horizontalTransportForm, horizontalTransport, ContinuousLinearMap.comp_apply,
      _root_.sum_apply, map_sum]
  rw [hsplit]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [associatedFormPivot_comp_scalarVectorMulL2]
  rfl

/-- The transport term `⟨w_⊥·∇_⊥b, φ⟩` is compact as a map `V → V*` whenever the horizontal
velocity coordinates vanish off a set of finite measure (the compactness paragraph of §2.3,
the case where the derivative falls on the input). -/
theorem isCompactOperator_horizontalTransportForm_of_ae_zero_off
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (w : WholePlaneC3LInf)
    (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0) :
    IsCompactOperator (horizontalTransportForm w) := by
  rw [horizontalTransportForm_eq_sum]
  refine isCompactOperator_finsetSum _ _ fun j => ?_
  have hloc : IsCompactOperator
      (wholePlaneC2LocalizationH1 (star (wholePlaneCoordLInf j.castSucc w))) :=
    isCompactOperator_wholePlaneC2LocalizationH1_of_ae_zero_off s hs hsm _
      (ae_zero_off_star (hw j))
  have hpivot : IsCompactOperator
      (associatedFormPivot
        (wholePlaneC2LocalizationH1 (star (wholePlaneCoordLInf j.castSucc w)))) :=
    isCompactOperator_associatedFormPivot_of_compact _ hloc
  have hcomp : IsCompactOperator
      ((associatedFormPivot
          (wholePlaneC2LocalizationH1 (star (wholePlaneCoordLInf j.castSucc w)))).comp
        (wholePlaneH1FirstDerivative C2 j)) :=
    hpivot.comp_clm (wholePlaneH1FirstDerivative C2 j)
  exact hcomp

/-- The divergence half of the stretching term, written with the velocity coefficient moved
onto the test slot. -/
theorem horizontalStretchDivergenceForm_eq_sum (w : WholePlaneC3LInf) :
    horizontalStretchDivergenceForm w =
      ∑ j : Fin 2, (associatedFormPivot
          ((wholePlaneScalarLocalizationH1
              (star (wholePlaneCoordLInf j.castSucc w))).comp
            (wholePlaneC2CoordH1 j))).comp horizontalDivergence := by
  have hdef : horizontalStretchDivergenceForm w =
      ∑ j : Fin 2,
        (associatedFormPivot ((wholePlaneC2CoordL2 j).comp (wholePlaneH1Embedding C2))).comp
          ((scalarVectorMulL2 (E := ℂ) volume (wholePlaneCoordLInf j.castSucc w)).comp
            horizontalDivergence) := rfl
  rw [hdef]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ContinuousLinearMap.comp_assoc, associatedFormPivot_comp_scalarVectorMulL2]
  rfl

/-- The divergence half `∫ w_⊥·(Div_⊥ b)conj φ` of the stretching term is compact as a map
`V → V*` for a velocity supported in a set of finite measure. -/
theorem isCompactOperator_horizontalStretchDivergenceForm_of_ae_zero_off
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (w : WholePlaneC3LInf)
    (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0) :
    IsCompactOperator (horizontalStretchDivergenceForm w) := by
  rw [horizontalStretchDivergenceForm_eq_sum]
  refine isCompactOperator_finsetSum _ _ fun j => ?_
  have hscalar : IsCompactOperator
      (wholePlaneScalarLocalizationH1 (star (wholePlaneCoordLInf j.castSucc w))) :=
    isCompactOperator_wholePlaneScalarLocalizationH1_of_ae_zero_off s hs hsm _
      (ae_zero_off_star (hw j))
  have hloc : IsCompactOperator
      ((wholePlaneScalarLocalizationH1 (star (wholePlaneCoordLInf j.castSucc w))).comp
        (wholePlaneC2CoordH1 j)) :=
    hscalar.comp_clm (wholePlaneC2CoordH1 j)
  have hpivot : IsCompactOperator
      (associatedFormPivot
        ((wholePlaneScalarLocalizationH1 (star (wholePlaneCoordLInf j.castSucc w))).comp
          (wholePlaneC2CoordH1 j))) :=
    isCompactOperator_associatedFormPivot_of_compact _ hloc
  have hcomp : IsCompactOperator
      ((associatedFormPivot
          ((wholePlaneScalarLocalizationH1 (star (wholePlaneCoordLInf j.castSucc w))).comp
            (wholePlaneC2CoordH1 j))).comp horizontalDivergence) :=
    hpivot.comp_clm horizontalDivergence
  exact hcomp

/-! ## Compactness of the full velocity form `K_w` -/

/-- **The velocity part `K_w` of the shifted form operator is compact** as a map `V → V*`
whenever the velocity vanishes almost everywhere off a set of finite measure
(the compactness paragraph of §2.3).  This is the input required by the analytic
Fredholm isolation. -/
theorem isCompactOperator_horizontalVelocityForm_of_ae_zero_off
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (N : ℝ) (w : WholePlaneC3LInf)
    (hw3 : ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf 2 w x = 0)
    (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0) :
    IsCompactOperator (horizontalVelocityForm N w) := by
  have h1 := isCompactOperator_horizontalTransportForm_of_ae_zero_off s hs hsm w hw
  have h2 := isCompactOperator_horizontalAxialForm_of_ae_zero_off s hs hsm N w hw3
  have h3 := isCompactOperator_horizontalStretchDivergenceForm_of_ae_zero_off s hs hsm w hw
  have h4 := isCompactOperator_horizontalStretchGradientForm_of_ae_zero_off s hs hsm w hw
  simpa [horizontalVelocityForm] using ((h1.add h2).add h3).add h4

/-! ## The Fredholm factorisation `𝔸_w(z) = F_z (1 - K(z))` -/

/-- The normalisation base point `z = 1` lies in the open right half plane. -/
theorem freeHorizontalBasePos : (0 : ℝ) < (1 : ℂ).re := by norm_num

/-- The inverse `F_1⁻¹ : V* → V` of the free form at the normalisation base point. -/
def freeHorizontalBaseInverse (N : ℝ) :
    ComplexAntiDual WholePlaneC2H1 →L[ℂ] WholePlaneC2H1 :=
  (freeHorizontalFormEquiv N freeHorizontalBasePos).symm.toContinuousLinearMap

/-- `F_1` undoes `F_1⁻¹`. -/
theorem freeHorizontalForm_baseInverse (N : ℝ) (u : ComplexAntiDual WholePlaneC2H1) :
    freeHorizontalForm N 1 (freeHorizontalBaseInverse N u) = u := by
  rw [← freeHorizontalFormEquiv_apply N freeHorizontalBasePos]
  exact (freeHorizontalFormEquiv N freeHorizontalBasePos).apply_symm_apply u

/-- The normalised free family `G_z = F_1⁻¹F_z : V → V`.  It is affine in `z`, hence entire,
and invertible exactly where `F_z` is. -/
def freeHorizontalNormalizer (N : ℝ) (z : ℂ) :
    WholePlaneC2H1 →L[ℂ] WholePlaneC2H1 :=
  (freeHorizontalBaseInverse N).comp (freeHorizontalForm N z)

/-- Composing the normaliser back with `F_1` returns `F_z`. -/
theorem freeHorizontalForm_normalizer (N : ℝ) (z : ℂ) (b : WholePlaneC2H1) :
    freeHorizontalForm N 1 (freeHorizontalNormalizer N z b) = freeHorizontalForm N z b :=
  freeHorizontalForm_baseInverse N (freeHorizontalForm N z b)

/-- The normalised free family is affine in the spectral parameter. -/
theorem freeHorizontalNormalizer_eq (N : ℝ) (z : ℂ) :
    freeHorizontalNormalizer N z =
      (freeHorizontalBaseInverse N).comp horizontalDirichletForm +
        ((N : ℂ) ^ 2 + z) • (freeHorizontalBaseInverse N).comp horizontalMassForm := by
  refine ContinuousLinearMap.ext fun b => ?_
  simp only [freeHorizontalNormalizer, freeHorizontalForm, ContinuousLinearMap.comp_apply,
    _root_.add_apply, _root_.smul_apply, map_add, map_smul]

/-- Being affine, the normalised free family is entire. -/
theorem analyticAt_freeHorizontalNormalizer (N : ℝ) (z : ℂ) :
    AnalyticAt ℂ (freeHorizontalNormalizer N) z := by
  have hfun : freeHorizontalNormalizer N = fun v : ℂ =>
      (freeHorizontalBaseInverse N).comp horizontalDirichletForm +
        ((N : ℂ) ^ 2 + v) • (freeHorizontalBaseInverse N).comp horizontalMassForm :=
    funext (freeHorizontalNormalizer_eq N)
  rw [hfun]
  have haffine : AnalyticAt ℂ (fun v : ℂ => (N : ℂ) ^ 2 + v) z :=
    analyticAt_const.add analyticAt_id
  exact analyticAt_const.add
    (analyticAt_smul_const haffine ((freeHorizontalBaseInverse N).comp horizontalMassForm))

/-- For `re z > 0` the normalised free family is an isomorphism of `V`. -/
def freeHorizontalNormalizerEquiv (N : ℝ) {z : ℂ} (hz : 0 < z.re) :
    WholePlaneC2H1 ≃L[ℂ] WholePlaneC2H1 :=
  (freeHorizontalFormEquiv N hz).trans
    (freeHorizontalFormEquiv N freeHorizontalBasePos).symm

/-- For `re z > 0` the normalised free family is invertible. -/
theorem freeHorizontalNormalizer_isInvertible (N : ℝ) {z : ℂ} (hz : 0 < z.re) :
    (freeHorizontalNormalizer N z).IsInvertible := by
  refine ⟨freeHorizontalNormalizerEquiv N hz, ?_⟩
  refine ContinuousLinearMap.ext fun b => ?_
  change (freeHorizontalFormEquiv N freeHorizontalBasePos).symm
      (freeHorizontalFormEquiv N hz b) = freeHorizontalNormalizer N z b
  rw [freeHorizontalFormEquiv_apply]
  rfl

/-- The normalised velocity form `F_1⁻¹K_w : V → V`, compact whenever `K_w` is. -/
def horizontalNormalizedVelocity (N : ℝ) (w : WholePlaneC3LInf) :
    WholePlaneC2H1 →L[ℂ] WholePlaneC2H1 :=
  (freeHorizontalBaseInverse N).comp (horizontalVelocityForm N w)

/-- The compact Fredholm kernel `K(z) = -F_z⁻¹K_w` of the paper's factorisation
`𝔸_w(z) = F_z(1 + F_z⁻¹K_w)` (analytic Fredholm paragraph of §2.3).  It is written
through the entire normalised family `G_z`, which makes it a total function of `z` and makes
its holomorphy a consequence of Mathlib's Neumann series. -/
def horizontalFredholmKernel (N : ℝ) (w : WholePlaneC3LInf) (z : ℂ) :
    WholePlaneC2H1 →L[ℂ] WholePlaneC2H1 :=
  -((freeHorizontalNormalizer N z).inverse.comp (horizontalNormalizedVelocity N w))

/-- The normalised velocity form is compact for a supported velocity. -/
theorem isCompactOperator_horizontalNormalizedVelocity_of_ae_zero_off
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (N : ℝ) (w : WholePlaneC3LInf)
    (hw3 : ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf 2 w x = 0)
    (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0) :
    IsCompactOperator (horizontalNormalizedVelocity N w) := by
  have hK := isCompactOperator_horizontalVelocityForm_of_ae_zero_off s hs hsm N w hw3 hw
  have h : IsCompactOperator
      ((freeHorizontalBaseInverse N).comp (horizontalVelocityForm N w)) :=
    hK.clm_comp (freeHorizontalBaseInverse N)
  exact h

/-- The Fredholm kernel is compact at every spectral parameter, for a supported velocity. -/
theorem isCompactOperator_horizontalFredholmKernel_of_ae_zero_off
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (N : ℝ) (w : WholePlaneC3LInf)
    (hw3 : ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf 2 w x = 0)
    (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0)
    (z : ℂ) : IsCompactOperator (horizontalFredholmKernel N w z) := by
  have h0 := isCompactOperator_horizontalNormalizedVelocity_of_ae_zero_off s hs hsm N w hw3 hw
  have h1 : IsCompactOperator
      ((freeHorizontalNormalizer N z).inverse.comp (horizontalNormalizedVelocity N w)) :=
    h0.clm_comp (freeHorizontalNormalizer N z).inverse
  have h2 : IsCompactOperator (horizontalFredholmKernel N w z) := h1.neg
  exact h2

/-- The Fredholm kernel is holomorphic in the operator norm at every `z` with `re z > 0`. -/
theorem analyticAt_horizontalFredholmKernel (N : ℝ) (w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) : AnalyticAt ℂ (horizontalFredholmKernel N w) z := by
  have hG : AnalyticAt ℂ (fun v : ℂ => (freeHorizontalNormalizer N v).inverse) z :=
    AnalyticFredholm.analyticAt_inverse (analyticAt_freeHorizontalNormalizer N z)
      (freeHorizontalNormalizer_isInvertible N hz)
  exact (analyticAt_clm_comp_const hG (horizontalNormalizedVelocity N w)).neg

/-- The Fredholm kernel is holomorphic on the open right half plane. -/
theorem analyticOnNhd_horizontalFredholmKernel (N : ℝ) (w : WholePlaneC3LInf) :
    AnalyticOnNhd ℂ (horizontalFredholmKernel N w) {z : ℂ | 0 < z.re} :=
  fun _ hz => analyticAt_horizontalFredholmKernel N w hz

/-- `F_z` undoes the normalised inverse: `F_z(G_z⁻¹(F_1⁻¹g)) = g` for `re z > 0`. -/
theorem freeHorizontalForm_normalizerInverse (N : ℝ) {z : ℂ} (hz : 0 < z.re)
    (g : ComplexAntiDual WholePlaneC2H1) :
    freeHorizontalForm N z
        ((freeHorizontalNormalizer N z).inverse (freeHorizontalBaseInverse N g)) = g := by
  have hself := (freeHorizontalNormalizer_isInvertible N hz).self_apply_inverse
    (freeHorizontalBaseInverse N g)
  have h1 := freeHorizontalForm_normalizer N z
    ((freeHorizontalNormalizer N z).inverse (freeHorizontalBaseInverse N g))
  have h3 : freeHorizontalForm N 1
        (freeHorizontalNormalizer N z
          ((freeHorizontalNormalizer N z).inverse (freeHorizontalBaseInverse N g))) =
      freeHorizontalForm N 1 (freeHorizontalBaseInverse N g) := by
    rw [hself]
  exact h1.symm.trans (h3.trans (freeHorizontalForm_baseInverse N g))

/-- **The paper's factorisation** `𝔸_w(z) = F_z(1 - K(z))` of the analytic Fredholm
paragraph of §2.3, with `K(z) = -F_z⁻¹K_w` the compact holomorphic family above. -/
theorem freeHorizontalForm_comp_compactPencil (N : ℝ) (w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) :
    (freeHorizontalForm N z).comp
        (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z) =
      horizontalPencilForm N w z := by
  refine ContinuousLinearMap.ext fun b => ?_
  have h1 : freeHorizontalForm N z (horizontalFredholmKernel N w z b) =
      -(freeHorizontalForm N z
        ((freeHorizontalNormalizer N z).inverse
          (freeHorizontalBaseInverse N (horizontalVelocityForm N w b)))) :=
    map_neg (freeHorizontalForm N z) _
  have hkey : freeHorizontalForm N z (horizontalFredholmKernel N w z b) =
      -(horizontalVelocityForm N w b) :=
    h1.trans (congrArg Neg.neg
      (freeHorizontalForm_normalizerInverse N hz (horizontalVelocityForm N w b)))
  calc ((freeHorizontalForm N z).comp
          (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z)) b
      = freeHorizontalForm N z (b - horizontalFredholmKernel N w z b) := rfl
    _ = freeHorizontalForm N z b -
          freeHorizontalForm N z (horizontalFredholmKernel N w z b) :=
      map_sub (freeHorizontalForm N z) _ _
    _ = freeHorizontalForm N z b - -(horizontalVelocityForm N w b) := by rw [hkey]
    _ = freeHorizontalForm N z b + horizontalVelocityForm N w b := sub_neg_eq_add _ _
    _ = horizontalPencilForm N w z b := rfl

/-- `F_z`, as a continuous linear map, is the forward map of the Lax-Milgram equivalence. -/
theorem freeHorizontalFormEquiv_coe (N : ℝ) {z : ℂ} (hz : 0 < z.re) :
    ((freeHorizontalFormEquiv N hz : WholePlaneC2H1 ≃L[ℂ] ComplexAntiDual WholePlaneC2H1) :
        WholePlaneC2H1 →L[ℂ] ComplexAntiDual WholePlaneC2H1) = freeHorizontalForm N z :=
  ContinuousLinearMap.ext (freeHorizontalFormEquiv_apply N hz)

/-- **The isolation criterion.**  For `re z > 0` the pencil `𝔸_w(z) = F_z + K_w` is an
isomorphism `V → V*` exactly when the compact pencil `1 - K(z)` is invertible on `V`.  This is
the reduction that §2.3 of the paper performs before invoking analytic
Fredholm theory. -/
theorem horizontalPencilForm_isInvertible_iff (N : ℝ) (w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) :
    (horizontalPencilForm N w z).IsInvertible ↔
      (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).IsInvertible := by
  rw [← freeHorizontalForm_comp_compactPencil N w hz, ← freeHorizontalFormEquiv_coe N hz]
  exact ContinuousLinearMap.isInvertible_equiv_comp

/-! ## The invertible base point and the local scalar reduction -/

/-- On the real axis the pencil is the Gårding-shifted form. -/
theorem horizontalPencilForm_ofReal (N : ℝ) (w : WholePlaneC3LInf) (alpha : ℝ) :
    horizontalPencilForm N w (alpha : ℂ) = horizontalShiftedWeakForm N w alpha := by
  refine ContinuousLinearMap.ext fun b => ContinuousLinearMap.ext fun phi => ?_
  rw [horizontalPencilForm_apply, horizontalShiftedWeakForm_apply]

/-- The Gårding shift is a strictly positive real number, hence a point of the right half
plane. -/
theorem horizontalGardingShift_pos (N : ℝ) (w : WholePlaneC3LInf) :
    0 < horizontalGardingShift N w := by
  have h := horizontalGardingConstant_nonneg N w
  unfold horizontalGardingShift
  linarith

/-- At the Gårding shift the pencil is coercive, hence an isomorphism `V → V*`: the
invertible base point required by analytic Fredholm isolation. -/
theorem horizontalPencilForm_isInvertible_gardingShift (N : ℝ) (w : WholePlaneC3LInf) :
    (horizontalPencilForm N w ((horizontalGardingShift N w : ℝ) : ℂ)).IsInvertible := by
  rw [horizontalPencilForm_ofReal]
  exact isInvertible_of_isComplexCoercive _
    (horizontalShiftedWeakForm_hasComplexCoercivityConstant N w).isComplexCoercive

/-- The compact pencil is invertible at the Gårding shift. -/
theorem compactPencil_isInvertible_gardingShift (N : ℝ) (w : WholePlaneC3LInf) :
    (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w)
      ((horizontalGardingShift N w : ℝ) : ℂ)).IsInvertible := by
  have hz : 0 < ((horizontalGardingShift N w : ℝ) : ℂ).re := by
    simpa using horizontalGardingShift_pos N w
  exact (horizontalPencilForm_isInvertible_iff N w hz).mp
    (horizontalPencilForm_isInvertible_gardingShift N w)

end HorizontalWeakForm

end

end FastDynamo

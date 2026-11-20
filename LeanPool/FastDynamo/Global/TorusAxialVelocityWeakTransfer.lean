/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusAxialVelocityConcrete
public import LeanPool.FastDynamo.Global.TorusChartFourierWeakTransfer

/-!
# Fourier weak transfer for the concrete added axial velocity

This module proves, rather than assumes, that the concrete axial fields
constructed in `TorusAxialVelocityConcrete` have the displayed derivatives
after descent to the transverse torus.  The proof follows the established
quotient-safe route: pull Fourier monomials to the Euclidean cover, use
whole-plane integration by parts for the compactly supported smooth
source, and transfer the resulting integrals through the canonical
fundamental domain.

The result is the Fourier weak-derivative identity `hasFourierWeakDerivative` for every axial
cell, together with its bundled real `L∞` value and derivative fields (`valueLInf`,
`derivativeLInf`); `Global/TorusFullVelocityConcrete.lean` sums them into the global axial
velocity.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set WithLp
open scoped BigOperators ENNReal Topology

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p} {supportRadius : ℝ}
variable (P : TorusCellPlacement (r := r) supportRadius)

namespace AxialWeakTransfer

open EuclideanCellSourceCertificate

/-! ## Euclidean scalar coordinates and compact support -/

/-- One complexified coordinate of the real Euclidean axial field, written
on `Fin 2 → ℝ` for the product fundamental-domain API. -/
def euclideanSourceCoord (tau : ℝ) (n : ℕ) (i : Fin 3)
    (x : Fin 2 → ℝ) : ℂ :=
  complexifyR3 (P.axialOffsetEuclidean tau n (finTwoToPair x)) i

/-- The corresponding complexified coordinate of the actual classical
derivative constructed in the concrete module. -/
def euclideanDerivativeCoord (tau : ℝ) (n : ℕ) (j : Fin 2) (i : Fin 3)
    (x : Fin 2 → ℝ) : ℂ :=
  complexifyR3
    (P.axialOffsetEuclideanDerivative tau n j (finTwoToPair x)) i

/-- The displayed derivative coordinate is the line derivative of
the Euclidean source coordinate. -/
theorem euclideanSourceCoord_hasLineDerivAt
    (tau : ℝ) (n : ℕ) (j : Fin 2) (i : Fin 3) (x : Fin 2 → ℝ) :
    HasLineDerivAt ℝ (euclideanSourceCoord P tau n i)
      (euclideanDerivativeCoord P tau n j i x) x
      (Pi.single j (1 : ℝ)) := by
  let projC : R3 →L[ℝ] ℂ :=
    ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).comp complexifyR3
  have hd : Differentiable ℝ (P.axialOffsetEuclidean tau n) :=
    (P.axialOffsetEuclidean_contDiff tau n).differentiable (by simp)
  have hsource := (hd (finTwoToPair x)).hasFDerivAt.comp x
    finTwoToPair.hasFDerivAt
  have hcoord := projC.hasFDerivAt.comp x hsource
  have hline := hcoord.hasLineDerivAt (Pi.single j (1 : ℝ))
  have hfun : euclideanSourceCoord P tau n i =
      projC ∘ P.axialOffsetEuclidean tau n ∘ finTwoToPair := by
    funext y
    rfl
  rw [hfun]
  apply hline.congr_deriv
  change complexifyR3
      (fderiv ℝ (P.axialOffsetEuclidean tau n) (finTwoToPair x)
        (finTwoToPair (Pi.single j (1 : ℝ)))) i = _
  rw [finTwoToPair_single,
    P.fderiv_axialOffsetEuclidean_apply_pairBasis tau n j]
  rfl

/-- Each complexified coordinate of the Euclidean axial cell field is continuous, the field
being smooth. -/
theorem continuous_euclideanSourceCoord
    (tau : ℝ) (n : ℕ) (i : Fin 3) :
    Continuous (euclideanSourceCoord P tau n i) := by
  have hsource : Continuous (P.axialOffsetEuclidean tau n) :=
    (P.axialOffsetEuclidean_contDiff tau n).continuous
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp
    (complexifyR3.continuous.comp (hsource.comp finTwoToPair.continuous))

/-- Each complexified coordinate of the displayed Euclidean derivative is measurable. -/
theorem measurable_euclideanDerivativeCoord
    (tau : ℝ) (n : ℕ) (j : Fin 2) (i : Fin 3) :
    Measurable (euclideanDerivativeCoord P tau n j i) := by
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).measurable.comp
    (complexifyR3.measurable.comp
      ((P.axialOffsetEuclideanDerivative_measurable tau n j).comp
        finTwoToPair.measurable))

/-- Nonzero axial source coordinates occur strictly inside the canonical
fundamental box because the entire placed buffer lies in the placement
chart. -/
theorem support_euclideanSourceCoord_subset_iocFundamentalBox
    (tau : ℝ) (n : ℕ) (i : Fin 3) :
    Function.support (euclideanSourceCoord P tau n i) ⊆
      iocFundamentalBox := by
  intro x hx
  have hbuffer : finTwoToPair x ∈ P.scaleFamily.bufferDisk n := by
    by_contra hnot
    have hz := P.axialOffsetEuclidean_eq_zero_of_not_mem_bufferDisk
      tau n hnot
    apply hx
    unfold euclideanSourceCoord
    rw [hz]
    simp
  have hchart := P.bufferDisk_subset_chart n hbuffer
  rw [ScaleFamily.placementChart, Set.mem_prod, finTwoToPair_apply] at hchart
  intro k
  fin_cases k
  · change x 0 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨hchart.1.1, by linarith [hchart.1.2]⟩
  · change x 1 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨by linarith [hchart.2.1], by linarith [hchart.2.2]⟩

/-- The displayed derivative coordinate vanishes outside the half-open unit fundamental box: it
is supported in the placed buffer disc, which the placement puts inside the chart. -/
theorem support_euclideanDerivativeCoord_subset_iocFundamentalBox
    (tau : ℝ) (n : ℕ) (j : Fin 2) (i : Fin 3) :
    Function.support (euclideanDerivativeCoord P tau n j i) ⊆
      iocFundamentalBox := by
  intro x hx
  have hbuffer : finTwoToPair x ∈ P.scaleFamily.bufferDisk n := by
    by_contra hnot
    have hz :=
      P.axialOffsetEuclideanDerivative_eq_zero_of_not_mem_bufferDisk
        tau n j hnot
    apply hx
    unfold euclideanDerivativeCoord
    rw [hz]
    simp
  have hchart := P.bufferDisk_subset_chart n hbuffer
  rw [ScaleFamily.placementChart, Set.mem_prod, finTwoToPair_apply] at hchart
  intro k
  fin_cases k
  · change x 0 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨hchart.1.1, by linarith [hchart.1.2]⟩
  · change x 1 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨by linarith [hchart.2.1], by linarith [hchart.2.2]⟩

/-- Each Euclidean source coordinate is integrable on the plane, being continuous with support in
the compact fundamental box. -/
theorem integrable_euclideanSourceCoord
    (tau : ℝ) (n : ℕ) (i : Fin 3) :
    Integrable (euclideanSourceCoord P tau n i) := by
  apply (continuous_euclideanSourceCoord P tau n i).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    isCompact_closedFundamentalBox
  exact (support_euclideanSourceCoord_subset_iocFundamentalBox P tau n i).trans
    iocFundamentalBox_subset_closedFundamentalBox

/-- Uniform pointwise bound on the Euclidean derivative coordinates:
`‖∂_j u_n^ax‖ ≤ ‖ϑ'‖_∞ (a_n / R_n)`, inherited componentwise from the vector bound. -/
theorem norm_euclideanDerivativeCoord_le
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) (j : Fin 2) (i : Fin 3)
    (x : Fin 2 → ℝ) :
    ‖euclideanDerivativeCoord P tau n j i x‖ ≤
      (axialPlateauLipschitzConstant : ℝ) *
        P.scaleFamily.axialGradientScale tau n := by
  calc
    ‖euclideanDerivativeCoord P tau n j i x‖ =
        ‖P.axialOffsetEuclideanDerivative tau n j
          (finTwoToPair x) i‖ := by
      simp [euclideanDerivativeCoord]
    _ ≤ ‖P.axialOffsetEuclideanDerivative tau n j (finTwoToPair x)‖ :=
      PiLp.norm_apply_le _ i
    _ ≤ (axialPlateauLipschitzConstant : ℝ) *
        P.scaleFamily.axialGradientScale tau n :=
      P.norm_axialOffsetEuclideanDerivative_le htau n j _

/-- Each Euclidean derivative coordinate is integrable, from the uniform bound together with
support in the compact fundamental box. -/
theorem integrable_euclideanDerivativeCoord
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) (j : Fin 2) (i : Fin 3) :
    Integrable (euclideanDerivativeCoord P tau n j i) := by
  have hfinite : volume (closedFundamentalBox : Set (Fin 2 → ℝ)) < ∞ :=
    isCompact_closedFundamentalBox.measure_lt_top
  have hon : IntegrableOn (euclideanDerivativeCoord P tau n j i)
      closedFundamentalBox := by
    exact IntegrableOn.of_bound hfinite
      (measurable_euclideanDerivativeCoord P tau n j i).aestronglyMeasurable.restrict
      ((axialPlateauLipschitzConstant : ℝ) *
        P.scaleFamily.axialGradientScale tau n)
      (Filter.Eventually.of_forall fun x ↦
        norm_euclideanDerivativeCoord_le P htau n j i x)
  apply hon.integrable_of_forall_notMem_eq_zero
  intro x hx
  by_contra hne
  exact hx ((support_euclideanDerivativeCoord_subset_iocFundamentalBox P
    tau n j i hne) |> iocFundamentalBox_subset_closedFundamentalBox)

/-! ## Euclidean integration by parts -/

/-- Whole-plane integration by parts against a Fourier monomial:
`∫ e^{-2πi m·x} ∂_j u = 2πi m_j ∫ e^{-2πi m·x} u`, for the compactly supported smooth axial cell
field.  This is the Euclidean input to the weak-derivative identity on the torus. -/
theorem integral_euclideanMonomial_mul_derivativeCoord
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ)
    (frequency : TransverseFrequency) (j : Fin 2) (i : Fin 3) :
    (∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x *
          euclideanDerivativeCoord P tau n j i x) =
      (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        ∫ x : Fin 2 → ℝ,
          euclideanMonomial (-frequency) x *
            euclideanSourceCoord P tau n i x :=
  integral_euclideanMonomial_mul_lineDerivative frequency j
    (integrable_euclideanSourceCoord P tau n i) (integrable_euclideanDerivativeCoord P htau n j i)
    (euclideanSourceCoord_hasLineDerivAt P tau n j i)

/-! ## Exact transfer through the quotient fundamental domain -/

/-- The descended axial field at a torus point represented inside the half-open unit box agrees
with the Euclidean field at that representative, both in the buffer disc (where periodization is
the identity) and outside it (where both vanish). -/
theorem axialOffsetTorus_transverseTorusPoint_eq_euclidean_of_mem_Ioc
    (tau : ℝ) (n : ℕ) {x : ℝ × ℝ}
    (hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1))
    (hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1)) :
    P.axialOffsetTorus tau n (transverseTorusPoint x) =
      P.axialOffsetEuclidean tau n x := by
  have hrep : transverseIocRepresentative (transverseTorusPoint x) = x :=
    transverseIocRepresentative_transverseTorusPoint_of_mem_Ioc hxzero hxone
  have hbuffer_iff : transverseTorusPoint x ∈ P.torusBufferDisk n ↔
      x ∈ P.scaleFamily.bufferDisk n := by
    rw [P.mem_torusBufferDisk_iff_transverseIocRepresentative n, hrep]
  by_cases hx : x ∈ P.scaleFamily.bufferDisk n
  · change P.periodizedExtension n (P.axialOffsetEuclidean tau n) x = _
    exact P.periodizedExtension_eq_source n _ hx
  · have hq : transverseTorusPoint x ∉ P.torusBufferDisk n :=
      hbuffer_iff.not.mpr hx
    rw [P.axialOffsetTorus_eq_zero_of_not_mem_buffer tau n hq,
      P.axialOffsetEuclidean_eq_zero_of_not_mem_bufferDisk tau n hx]

/-- The descended displayed derivative at a torus point represented inside the half-open unit box
agrees with the Euclidean derivative at that representative. -/
theorem axialOffsetTorusDerivative_transverseTorusPoint_eq_euclidean_of_mem_Ioc
    (tau : ℝ) (n : ℕ) (j : Fin 2) {x : ℝ × ℝ}
    (hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1))
    (hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1)) :
    P.axialOffsetTorusDerivative tau n j (transverseTorusPoint x) =
      P.axialOffsetEuclideanDerivative tau n j x := by
  have hrep : transverseIocRepresentative (transverseTorusPoint x) = x :=
    transverseIocRepresentative_transverseTorusPoint_of_mem_Ioc hxzero hxone
  have hbuffer_iff : transverseTorusPoint x ∈ P.torusBufferDisk n ↔
      x ∈ P.scaleFamily.bufferDisk n := by
    rw [P.mem_torusBufferDisk_iff_transverseIocRepresentative n, hrep]
  by_cases hx : x ∈ P.scaleFamily.bufferDisk n
  · change P.periodizedExtension n
      (P.axialOffsetEuclideanDerivative tau n j) x = _
    exact P.periodizedExtension_eq_source n _ hx
  · have hq : transverseTorusPoint x ∉ P.torusBufferDisk n :=
      hbuffer_iff.not.mpr hx
    rw [P.axialOffsetTorusDerivative_eq_zero_of_not_mem_buffer tau n j hq,
      P.axialOffsetEuclideanDerivative_eq_zero_of_not_mem_bufferDisk
        tau n j hx]

/-- Transfer of the value pairing from the torus to the plane: the torus integral of
`e^{-2πi m·q}` against a coordinate of the descended axial field equals the corresponding
Euclidean integral, since the fundamental box is a fundamental domain and the field is supported
in it. -/
theorem torusIntegral_mFourier_mul_sourceCoord_eq_euclidean
    (tau : ℝ) (n : ℕ) (frequency : TransverseFrequency) (i : Fin 3) :
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q *
          complexifyR3 (P.axialOffsetTorus tau n q) i
          ∂transverseMeasure) =
      ∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x *
          euclideanSourceCoord P tau n i x :=
  torusIntegral_mFourier_mul_eq_euclidean frequency
    (support_euclideanSourceCoord_subset_iocFundamentalBox P tau n i)
    (fun _ hx0 hx1 ↦ congrArg (fun value ↦ complexifyR3 value i)
      (axialOffsetTorus_transverseTorusPoint_eq_euclidean_of_mem_Ioc P tau n hx0 hx1))

/-- Transfer of the derivative pairing from the torus to the plane: the torus integral of
`e^{-2πi m·q}` against a coordinate of the descended displayed derivative equals the
corresponding Euclidean integral. -/
theorem torusIntegral_mFourier_mul_derivativeCoord_eq_euclidean
    (tau : ℝ) (n : ℕ) (frequency : TransverseFrequency)
    (j : Fin 2) (i : Fin 3) :
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q *
          complexifyR3 (P.axialOffsetTorusDerivative tau n j q) i
          ∂transverseMeasure) =
      ∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x *
          euclideanDerivativeCoord P tau n j i x :=
  torusIntegral_mFourier_mul_eq_euclidean frequency
    (support_euclideanDerivativeCoord_subset_iocFundamentalBox P tau n j i)
    (fun _ hx0 hx1 ↦ congrArg (fun value ↦ complexifyR3 value i)
      (axialOffsetTorusDerivative_transverseTorusPoint_eq_euclidean_of_mem_Ioc P tau n j hx0 hx1))

/-! ## Real `L∞` fields -/

/-- The descended axial cell field is essentially bounded, by its uniform pointwise bound `a_n`. -/
theorem axialOffsetTorus_memLp_top
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) :
    MemLp (P.axialOffsetTorus tau n) ∞ transverseMeasure :=
  memLp_top_of_bound
    (P.measurable_axialOffsetTorus tau n).aestronglyMeasurable
    (P.scaleFamily.axialAmplitude tau n)
    (Filter.Eventually.of_forall (P.norm_axialOffsetTorus_le htau n))

/-- Each descended displayed derivative is essentially bounded, by its uniform pointwise bound
`‖ϑ'‖_∞ (a_n / R_n)`. -/
theorem axialOffsetTorusDerivative_memLp_top
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) (j : Fin 2) :
    MemLp (P.axialOffsetTorusDerivative tau n j) ∞ transverseMeasure :=
  memLp_top_of_bound
    (P.measurable_axialOffsetTorusDerivative tau n j).aestronglyMeasurable
    ((axialPlateauLipschitzConstant : ℝ) *
      P.scaleFamily.axialGradientScale tau n)
    (Filter.Eventually.of_forall
      (P.norm_axialOffsetTorusDerivative_le htau n j))

/-- The bundled real value of one axial cell. -/
def valueLInf {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) :
    TransverseR3LInf :=
  (axialOffsetTorus_memLp_top P htau n).toLp
    (P.axialOffsetTorus tau n)

/-- One bundled real derivative of the axial cell. -/
def derivativeLInf {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ)
    (j : Fin 2) : TransverseR3LInf :=
  (axialOffsetTorusDerivative_memLp_top P htau n j).toLp
    (P.axialOffsetTorusDerivative tau n j)

/-- The bundled `L∞` class of the axial cell value is represented a.e. by the pointwise field
`axialOffsetTorus`. -/
theorem valueLInf_coe_ae
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) :
    (valueLInf P htau n : TransverseTorus → R3)
      =ᵐ[transverseMeasure] P.axialOffsetTorus tau n :=
  MemLp.coeFn_toLp _

/-- The bundled `L∞` class of the axial cell derivative is represented a.e. by the pointwise field
`axialOffsetTorusDerivative`. -/
theorem derivativeLInf_coe_ae
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) (j : Fin 2) :
    (derivativeLInf P htau n j : TransverseTorus → R3)
      =ᵐ[transverseMeasure] P.axialOffsetTorusDerivative tau n j :=
  MemLp.coeFn_toLp _

/-- The `L∞` norm of the axial cell value is at most the cell's axial amplitude `a_n`. -/
theorem norm_valueLInf_le
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) :
    ‖valueLInf P htau n‖ ≤ P.scaleFamily.axialAmplitude tau n := by
  rw [valueLInf, Lp.norm_toLp]
  have ha : 0 ≤ P.scaleFamily.axialAmplitude tau n := by
    unfold ScaleFamily.axialAmplitude
    exact mul_nonneg (div_nonneg htau p.wavenumber_pos.le)
      (P.scaleFamily.ell_pos n).le
  apply ENNReal.toReal_le_of_le_ofReal ha
  rw [eLpNorm_exponent_top (axialOffsetTorus_memLp_top P htau n).aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound
    (Filter.Eventually.of_forall (P.norm_axialOffsetTorus_le htau n))

/-- The `L∞` norm of an axial cell derivative is at most `‖ϑ'‖_∞ (a_n / R_n)`, the paper's
added-axial gradient bound (§3.3, after `eq:axial-offset`). -/
theorem norm_derivativeLInf_le
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) (j : Fin 2) :
    ‖derivativeLInf P htau n j‖ ≤
      (axialPlateauLipschitzConstant : ℝ) *
        P.scaleFamily.axialGradientScale tau n := by
  rw [derivativeLInf, Lp.norm_toLp]
  have hg : 0 ≤ P.scaleFamily.axialGradientScale tau n := by
    rw [P.scaleFamily.axialGradientScale_formula tau n]
    exact mul_nonneg (div_nonneg htau p.wavenumber_pos.le)
      (P.scaleFamily.bufferRadius_nonneg n)
  apply ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (NNReal.coe_nonneg _) hg)
  rw [eLpNorm_exponent_top (axialOffsetTorusDerivative_memLp_top P htau n j).aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound
    (Filter.Eventually.of_forall
      (P.norm_axialOffsetTorusDerivative_le htau n j))

/-- The complexified `L∞` value class is represented a.e. by the pointwise complexification of the
real axial field. -/
theorem complexifyR3LTwo_valueLInf_coe_ae
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) :
    (complexifyR3LTwo (valueLInf P htau n) : TransverseTorus → C3)
      =ᵐ[transverseMeasure]
        fun q ↦ complexifyR3 (P.axialOffsetTorus tau n q) := by
  filter_upwards [complexifyR3LTwo_coe_ae (valueLInf P htau n),
    valueLInf_coe_ae P htau n] with q hcomplex hvalue
  rw [hcomplex, hvalue]
  rfl

/-- The complexified `L∞` derivative class is represented a.e. by the pointwise complexification
of the real displayed derivative. -/
theorem complexifyR3LTwo_derivativeLInf_coe_ae
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) (j : Fin 2) :
    (complexifyR3LTwo (derivativeLInf P htau n j) :
        TransverseTorus → C3)
      =ᵐ[transverseMeasure]
        fun q ↦ complexifyR3 (P.axialOffsetTorusDerivative tau n j q) := by
  filter_upwards [complexifyR3LTwo_coe_ae
      (derivativeLInf P htau n j),
    derivativeLInf_coe_ae P htau n j] with q hcomplex hderiv
  rw [hcomplex, hderiv]
  rfl

/-! ## Fourier coefficients and the weak derivative identity -/

/-- The transverse Fourier coefficient of a coordinate of the complexified value is the torus
integral of `e^{-2πi m·q}` against that coordinate. -/
theorem transverseCoeffCLM_complexify_value_eq_torusIntegral
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ)
    (frequency : TransverseFrequency) (i : Fin 3) :
    transverseCoeffCLM frequency i
        (complexifyR3LTwo (valueLInf P htau n)) =
      ∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q *
          complexifyR3 (P.axialOffsetTorus tau n q) i
          ∂transverseMeasure := by
  rw [← transverseMonomialComponentPairing_eq_coeff,
    transverseMonomialComponentPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [transverseMonomialL2_coe_ae frequency,
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
      (complexifyR3LTwo (valueLInf P htau n)),
    complexifyR3LTwo_valueLInf_coe_ae P htau n]
      with q hmono hcoord hvalue
  change ((transverseCoordL2 i
      (complexifyR3LTwo (valueLInf P htau n)) : TransverseScalarL2) :
        TransverseTorus → ℂ) q = _ at hcoord
  rw [hmono, hcoord, hvalue]
  rw [← UnitAddTorus.mFourier_neg]
  rfl

/-- The transverse Fourier coefficient of a coordinate of the complexified displayed derivative is
the torus integral of `e^{-2πi m·q}` against that coordinate. -/
theorem transverseCoeffCLM_complexify_derivative_eq_torusIntegral
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ)
    (frequency : TransverseFrequency) (j : Fin 2) (i : Fin 3) :
    transverseCoeffCLM frequency i
        (complexifyR3LTwo (derivativeLInf P htau n j)) =
      ∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q *
          complexifyR3 (P.axialOffsetTorusDerivative tau n j q) i
          ∂transverseMeasure := by
  rw [← transverseMonomialComponentPairing_eq_coeff,
    transverseMonomialComponentPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [transverseMonomialL2_coe_ae frequency,
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
      (complexifyR3LTwo (derivativeLInf P htau n j)),
    complexifyR3LTwo_derivativeLInf_coe_ae P htau n j]
      with q hmono hcoord hderiv
  change ((transverseCoordL2 i
      (complexifyR3LTwo (derivativeLInf P htau n j)) :
        TransverseScalarL2) : TransverseTorus → ℂ) q = _ at hcoord
  rw [hmono, hcoord, hderiv]
  rw [← UnitAddTorus.mFourier_neg]
  rfl

/-- The quotient-periodized displayed derivative is the Fourier
weak derivative of the concrete axial cell. -/
theorem hasFourierWeakDerivative
    {tau : ℝ} (htau : 0 ≤ tau) (n : ℕ) (j : Fin 2) :
    HasTransverseFourierDerivative j
      (complexifyR3LTwo (valueLInf P htau n))
      (complexifyR3LTwo (derivativeLInf P htau n j)) := by
  intro frequency i
  calc
    transverseCoeffCLM frequency i
        (complexifyR3LTwo (derivativeLInf P htau n j)) =
        ∫ q : TransverseTorus,
          UnitAddTorus.mFourier (-frequency) q *
            complexifyR3
              (P.axialOffsetTorusDerivative tau n j q) i
            ∂transverseMeasure :=
      transverseCoeffCLM_complexify_derivative_eq_torusIntegral
        P htau n frequency j i
    _ = ∫ x : Fin 2 → ℝ,
          euclideanMonomial (-frequency) x *
            euclideanDerivativeCoord P tau n j i x :=
      torusIntegral_mFourier_mul_derivativeCoord_eq_euclidean
        P tau n frequency j i
    _ = (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
          ∫ x : Fin 2 → ℝ,
            euclideanMonomial (-frequency) x *
              euclideanSourceCoord P tau n i x :=
      integral_euclideanMonomial_mul_derivativeCoord
        P htau n frequency j i
    _ = (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
          ∫ q : TransverseTorus,
            UnitAddTorus.mFourier (-frequency) q *
              complexifyR3 (P.axialOffsetTorus tau n q) i
              ∂transverseMeasure := by
      rw [torusIntegral_mFourier_mul_sourceCoord_eq_euclidean
        P tau n frequency i]
    _ = (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
          transverseCoeffCLM frequency i
            (complexifyR3LTwo (valueLInf P htau n)) := by
      rw [transverseCoeffCLM_complexify_value_eq_torusIntegral
        P htau n frequency i]

end AxialWeakTransfer

end ScaleFamily.TorusCellPlacement

end

end FastDynamo

/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusSelectedWitness
public import LeanPool.FastDynamo.Global.TorusSelectedCellParametrixData

/-!
# `eq:selected-contour-identity`

The proof of `lem:global-riesz-nonzero`.  Testing the
approximate inverse `eq:Rapp` against the placed witness `f_n` of
`FastDynamo/Global/TorusSelectedWitness.lean` kills the background summand and strips every
cut-off and chart transport from the selected summand:

`⟨cR_app(z) f_n, f_n⟩ = ⟨(z + iτ - cL_{δ_n})^{-1} f_*, f_*⟩`,  `z ∈ Γ_τ`,

because `(1 - φ_n) f_n = 0`, because `⟨ψ_n g, f_n⟩ = ⟨g, f_n⟩`, and because the scaling
identity `eq:scaling` conjugates the selected resolvent by the `L²` isometry `U_n`.  Integrating
around `Γ_τ` and translating the contour variable by `iτ` gives `eq:selected-contour-identity`

`(2πi)^{-1} ∫_{Γ_τ} ⟨cR_app(z) f_n, f_n⟩ dz = ⟨P_{δ_n} f_*, f_*⟩`.

The paper's inner products are linear in the first argument and it tests as `⟨T f_n, f_n⟩`.
Here inner products are written in the second slot (`⟨f, T f⟩`), where Mathlib's inner product
is complex **linear** in the operator, so that the whole contour manipulation is one application of
`circleIntegral.map` to the bounded functional `innerTest f`.  The real parts of the two
conventions agree (`re_inner_comm`), which is all `lem:global-riesz-nonzero` uses.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex MeasureTheory Metric Set

namespace TorusSelectedContourIdentity

open HorizontalCutoffCommutator
open ParametrixCutoffs
open ParametrixNeumannCorrection
open TorusChartActionBridge
open TorusChartC2Transfer
open LocalizedSummandAlgebra
open TorusParametrixError
open TorusPlacedCutoffC2
open TorusSelectedWitness
open TorusTwoSummandParametrix
open TransverseSmoothBumpPeriodization

/-! ## The bounded test functional `T ↦ ⟨f, T f⟩` -/

/-- The bounded complex-linear functional `T ↦ ⟨f, T f⟩` on operators.  Unlike `T ↦ ⟨T f, f⟩` it
is complex linear, which is what lets it pass through a contour integral. -/
def innerTest {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : E) :
    (E →L[ℂ] E) →L[ℂ] ℂ :=
  (innerSL ℂ f).comp (ContinuousLinearMap.apply ℂ E f)

/-- The test functional, evaluated. -/
@[simp] theorem innerTest_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : E) (T : E →L[ℂ] E) : innerTest f T = (inner ℂ f (T f) : ℂ) :=
  rfl

/-- The two orders of the test inner product have the same real part. -/
theorem re_inner_comm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : E) (T : E →L[ℂ] E) :
    (inner ℂ (T f) f : ℂ).re = (inner ℂ f (T f) : ℂ).re := by
  rw [← inner_conj_symm (𝕜 := ℂ) (T f) f, Complex.conj_re]

/-! ## Translation of a circle integral -/

/-- Translating the centre of a circle and the argument of the integrand by opposite constants
leaves the circle integral unchanged. -/
theorem circleIntegral_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (c a : ℂ) (R : ℝ) :
    (∮ z in C(c - a, R), f (z + a)) = ∮ z in C(c, R), f z := by
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro theta _
  have harg : circleMap (c - a) R theta + a = circleMap c R theta := by
    simp only [circleMap]
    ring
  simp only [deriv_circleMap, harg]

/-! ## The pointwise identity of `eq:selected-contour-identity` -/

section Pointwise

variable {u ubg : TransverseRealW1Inf} {eps : ℝ} {K : ℤ} {Rn : ℝ} {S : Set ℂ}

/-- **The test identity for `eq:Rapp`**, as used in the proof of `lem:global-riesz-nonzero`.
On a state fixed by the input cut-off
the background summand of the approximate inverse contributes nothing, and the selected summand
loses both the output cut-off and the chart transport. -/
theorem inner_stateParametrix_eq_of_witness
    (P : TwoSummandParametrixData WholePlaneC2L2 WholePlaneC2H2 u ubg eps K Rn S)
    {fn : TransverseC2L2} {g0 : WholePlaneC2L2}
    (hphi : P.cutoffs.input.stateMul fn = fn)
    (hrestrict : P.selected.restrictInput fn = g0)
    (hstate : ∀ w : WholePlaneC2L2, (inner ℂ fn (P.selected.extendState w) : ℂ) = inner ℂ g0 w)
    (z : ℂ) :
    (inner ℂ fn (transverseH2Embedding (P.approximateInverse z fn)) : ℂ) =
      inner ℂ g0 (P.selected.localOperator.embedding (P.selected.resolvent z g0)) := by
  have hcomp : P.cutoffs.inputComplement fn = 0 := by
    change fn - P.cutoffs.input.stateMul fn = 0
    rw [hphi, sub_self]
  have hsplit : P.approximateInverse z fn =
      P.cutoffs.background.domainMul (P.background.resolvent z (P.cutoffs.inputComplement fn)) +
        P.selected.extendDomain (P.selected.resolvent z (P.selected.restrictInput fn)) := by
    simp only [TwoSummandParametrixData.approximateInverse, twoSummandParametrix,
      localSummand, add_apply, ContinuousLinearMap.comp_apply]
  have hinner : P.background.resolvent z (P.cutoffs.inputComplement fn) = 0 :=
    (congrArg (P.background.resolvent z) hcomp).trans (map_zero _)
  have hbg : P.cutoffs.background.domainMul
      (P.background.resolvent z (P.cutoffs.inputComplement fn)) = 0 :=
    (congrArg P.cutoffs.background.domainMul hinner).trans (map_zero _)
  have hval : P.approximateInverse z fn =
      P.selected.extendDomain (P.selected.resolvent z g0) := by
    rw [hsplit, hbg, zero_add]
    exact congrArg P.selected.extendDomain (congrArg (P.selected.resolvent z) hrestrict)
  have hemb := DFunLike.congr_fun P.selected.embedding_intertwining
    (P.selected.resolvent z g0)
  have hemb' : transverseH2Embedding
        (P.selected.extendDomain (P.selected.resolvent z g0)) =
      P.selected.extendState
        (P.selected.localOperator.embedding (P.selected.resolvent z g0)) := by
    simpa only [ContinuousLinearMap.comp_apply, horizontalInductionOperator_embedding]
      using hemb
  calc (inner ℂ fn (transverseH2Embedding (P.approximateInverse z fn)) : ℂ)
      = inner ℂ fn (transverseH2Embedding
          (P.selected.extendDomain (P.selected.resolvent z g0))) :=
        congrArg (fun x ↦ (inner ℂ fn (transverseH2Embedding x) : ℂ)) hval
    _ = inner ℂ fn (P.selected.extendState
          (P.selected.localOperator.embedding (P.selected.resolvent z g0))) :=
        congrArg (fun x ↦ (inner ℂ fn x : ℂ)) hemb'
    _ = inner ℂ g0 (P.selected.localOperator.embedding (P.selected.resolvent z g0)) :=
        hstate _

end Pointwise

/-! ## The contour identity -/

section Generic

universe ux ud

variable {X : Type ux} {D : Type ud}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]

omit [CompleteSpace D] in
/-- The test functional passes through the normalized contour operator of a parametrix. -/
theorem innerTest_contourOperator (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D)
    (c : ℂ) (r : ℝ) (f : X) (hInt : CircleIntegrable (stateParametrix A R) c r) :
    innerTest f (contourOperator A R c r) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ z in C(c, r), innerTest f (stateParametrix A R z)) := by
  rw [contourOperator, map_smul]
  exact congrArg _ (circleIntegral.map (innerTest f) hInt).symm

omit [CompleteSpace D] in
/-- The test functional passes through a Riesz contour projection. -/
theorem innerTest_rieszProjection {A : DomainOperator X D} {c : ℂ} {r : ℝ}
    (h : HasResolventOn A (Metric.sphere c r)) (f : X) (hr : 0 ≤ r) :
    innerTest f h.rieszProjection =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ z in C(c, r), innerTest f (h.stateResolvent z)) := by
  have hrp : h.rieszProjection =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • circleIntegral h.stateResolvent c r := rfl
  rw [hrp, map_smul]
  exact congrArg _
    (circleIntegral.map (innerTest f) (h.circleIntegrable_stateResolvent hr)).symm

end Generic

section Contour

variable {u ubg : TransverseRealW1Inf} {eps : ℝ} {K : ℤ} {Rn tau : ℝ}

/-- **`eq:selected-contour-identity`**, in abstract
form.  If the approximate inverse tests against `f_n` exactly as the local resolvent tests
against `f_*` at every point of `Γ_τ`, then the normalized contour operator of `eq:Rapp` tests
against `f_n` exactly as the local Riesz projection tests against `f_*`.  The contour variable is
translated by `iτ`, which is the only place where `Γ_τ = Γ - iτ` is used. -/
theorem inner_contourOperator_eq_of_pointwise (Gamma : SpectralCircle)
    (P : TwoSummandParametrixData WholePlaneC2L2 WholePlaneC2H2 u ubg eps K Rn
      (verticallyShiftedSet tau Gamma.boundary))
    {A0 : DomainOperator WholePlaneC2L2 WholePlaneC2H2}
    (hloc : HasResolventOn A0 Gamma.boundary)
    (fn : TransverseC2L2) (fstar : WholePlaneC2L2)
    (hpoint : ∀ z ∈ (backgroundShiftedContour Gamma tau).boundary,
      (inner ℂ fn (transverseH2Embedding (P.approximateInverse z fn)) : ℂ) =
        inner ℂ fstar (hloc.stateResolvent (z + Complex.I * (tau : ℂ)) fstar)) :
    (inner ℂ fn (contourOperator (horizontalInductionOperator u eps K) P.approximateInverse
        (backgroundShiftedContour Gamma tau).center Gamma.radius fn) : ℂ) =
      inner ℂ fstar (hloc.rieszProjection fstar) := by
  have hr : (0 : ℝ) ≤ Gamma.radius := Gamma.radius_pos.le
  have hcont : ContinuousOn P.approximateInverse
      (Metric.sphere (backgroundShiftedContour Gamma tau).center Gamma.radius) := by
    refine P.continuousOn_approximateInverse.mono ?_
    rw [verticallyShiftedSet_boundary]
    exact subset_rfl
  have hInt : CircleIntegrable (stateParametrix (horizontalInductionOperator u eps K)
      P.approximateInverse) (backgroundShiftedContour Gamma tau).center Gamma.radius :=
    (continuousOn_stateParametrix _ _ hcont).circleIntegrable hr
  have hSP : ∀ z : ℂ, innerTest fn (stateParametrix (horizontalInductionOperator u eps K)
        P.approximateInverse z) =
      (inner ℂ fn (transverseH2Embedding (P.approximateInverse z fn)) : ℂ) := fun _ ↦ rfl
  have hmid : (∮ z in C((backgroundShiftedContour Gamma tau).center, Gamma.radius),
        innerTest fn (stateParametrix (horizontalInductionOperator u eps K)
          P.approximateInverse z)) =
      ∮ w in C(Gamma.center, Gamma.radius), innerTest fstar (hloc.stateResolvent w) :=
    (circleIntegral.integral_congr hr fun z hz ↦ (hSP z).trans (hpoint z hz)).trans
      (circleIntegral_translate (fun w ↦ innerTest fstar (hloc.stateResolvent w)) Gamma.center
        (Complex.I * (tau : ℂ)) Gamma.radius)
  have hA := innerTest_contourOperator (horizontalInductionOperator u eps K)
    P.approximateInverse (backgroundShiftedContour Gamma tau).center Gamma.radius fn hInt
  have hB := innerTest_rieszProjection hloc fstar hr
  change innerTest fn (contourOperator (horizontalInductionOperator u eps K) P.approximateInverse
    (backgroundShiftedContour Gamma tau).center Gamma.radius) = innerTest fstar hloc.rieszProjection
  rw [hA, hB]
  exact congrArg _ hmid

end Contour

/-! ## The selected cell -/

section SelectedCell

variable {v : WholePlaneVelocityCoefficients} {s : WholePlaneExactScalingParameters}
  {u ubg : TransverseRealW1Inf} {p : WholePlane} {R deltaUpper bound : ℝ}
  {Gamma : SpectralCircle}

/-- **All the data of one selected cell** that `sec:parametrix` consumes, bundled: the chart
geometry (`eq:chart-packing`), the seed's uniform local resolvent bound
(`cor:scaled-local-resolvents`), the background resolvent datum (`prop:background-resolvent`),
and the three velocity hypotheses of `lem:parametrix-error` together with the chart coefficient
agreement on the selected cell used in its proof.  These are exactly the arguments of
`TorusChartC2Transfer.selectedCellParametrixData`; bundling them keeps the statements of
`lem:global-riesz-nonzero` and `prop:global-spectral-transfer` readable. -/
structure SelectedCellData (v : WholePlaneVelocityCoefficients)
    (s : WholePlaneExactScalingParameters) (u ubg : TransverseRealW1Inf) (p : WholePlane)
    (R deltaUpper bound : ℝ) (Gamma : SpectralCircle) where
  /-- The reserved radius of the cell is positive. -/
  radius_pos : 0 < R
  /-- The closed half-buffer disc does not wrap around the torus (`eq:chart-packing`). -/
  box : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox
  /-- The closed three-quarter buffer disc does not wrap around the torus either. -/
  boxAux : Metric.closedBall p (auxOutputRadius R / 2) ⊆ TorusChartL2.wholePlaneFundamentalBox
  /-- The seed's uniform `L² → H²` resolvent bound on `Γ`; the paper states its `L² → H¹`
  corollary as `eq:local-continuation-bound`. -/
  localBound : WholePlaneLocalResolventBound v s.N s.delta Gamma.boundary bound
  /-- The seed bound is nonnegative. -/
  bound_nonneg : 0 ≤ bound
  /-- The physical diffusivity is nonnegative. -/
  epsilon_nonneg : 0 ≤ s.epsilon
  /-- The rescaled diffusivity is nonnegative. -/
  delta_nonneg : 0 ≤ s.delta
  /-- The rescaled diffusivity lies below the right endpoint of the seed's interval. -/
  delta_le : s.delta ≤ deltaUpper
  /-- The global and the placed local velocity coefficients agree on `supp auxiliaryCutoff_n`. -/
  agree : ChartCoefficientAgreement (Metric.closedBall p (auxOutputRadius R / 2)) u
    (rescaledWholePlaneVelocityCoefficients v p s.ell s.ell_pos) s.a
  /-- The background resolvent datum on `Γ_τ` (`prop:background-resolvent`). -/
  background : BackgroundParametrixData ubg s.epsilon s.K
    (verticallyShiftedSet s.tau Gamma.boundary)
  /-- Inner radius of the velocity localisation. -/
  innerRadius : ℝ
  /-- Outer radius of the velocity localisation. -/
  outerRadius : ℝ
  /-- The inner radius is at most `R_n/10` (`eq:local-support-in-buffer`). -/
  inner_le : innerRadius ≤ R / 10
  /-- The outer radius is at least `R_n/2`. -/
  outer_ge : R / 2 ≤ outerRadius
  /-- The transverse velocity is localised in the core, up to the exterior tail. -/
  localized : TransverseVelocityLocalized p innerRadius outerRadius u
  /-- The full and background velocity coordinates agree off the core. -/
  value_agree : ∀ i : Fin 3, ∀ᵐ q ∂transverseMeasure,
    dist (wholePlaneIocRepresentative q) p ≤ R / 10 ∨
      (transverseW1InfComplexValueCoordLInf i u) q =
        (transverseW1InfComplexValueCoordLInf i ubg) q
  /-- The full and background velocity gradients agree off the core. -/
  deriv_agree : ∀ j : Fin 2, ∀ᵐ q ∂transverseMeasure,
    dist (wholePlaneIocRepresentative q) p ≤ R / 10 ∨
      (transverseW1InfHorizontalDerivLInf j u) q =
        (transverseW1InfHorizontalDerivLInf j ubg) q

namespace SelectedCellData

variable (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma)

/-- **`eq:Rapp` at the selected cell**, assembled from the bundled data. -/
def parametrix : TwoSummandParametrixData WholePlaneC2L2 WholePlaneC2H2 u ubg s.epsilon s.K R
    (verticallyShiftedSet s.tau Gamma.boundary) :=
  selectedCellParametrixData C.radius_pos C.box C.boxAux C.localBound C.bound_nonneg
    C.epsilon_nonneg C.delta_nonneg C.delta_le C.agree C.background C.inner_le C.outer_ge
    C.localized C.value_agree C.deriv_agree

/-- The selected resolvent of the assembled datum is `R_n(z) = U_n R_{δ_n}(z + iτ) U_n⁻¹`. -/
theorem parametrix_resolvent (z : ℂ) :
    C.parametrix.selected.resolvent z = scaledLocalResolventInv v p s C.localBound z := rfl

/-- The domain embedding of the selected local model is the whole-plane `H²` inclusion. -/
theorem parametrix_localEmbedding :
    C.parametrix.selected.localOperator.embedding = wholePlaneH2Embedding C2 := rfl

end SelectedCellData

end SelectedCell

/-! ## `eq:selected-contour-identity` at the selected cell -/

section CellWitness

variable {v : WholePlaneVelocityCoefficients} {s : WholePlaneExactScalingParameters}
  {u ubg : TransverseRealW1Inf} {p : WholePlane} {R deltaUpper bound Lstar : ℝ}
  {Gamma : SpectralCircle}

/-- **The pointwise half of `eq:selected-contour-identity`** (the display before it in the proof
of `lem:global-riesz-nonzero`): testing `eq:Rapp` against the placed witness returns the local
resolvent tested against the seed witness, at every spectral parameter.  The background summand
dies on `(1 - φ_n) f_n = 0`, the output cut-off is invisible to `f_n`, and the scaling identity
`eq:scaling` removes the unitary `U_n`. -/
theorem inner_stateParametrix_placedWitness
    (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma) (fstar : WholePlaneC2L2)
    (hsupp : ∀ᵐ y ∂volume, Lstar < ‖y‖ → (fstar : WholePlane → C2) y = 0)
    (hfit : Lstar * s.ell ≤ R / 5) (z : ℂ) :
    (inner ℂ (placedWitness p R C.radius_pos s.ell s.ell_pos fstar)
        (transverseH2Embedding (C.parametrix.approximateInverse z
          (placedWitness p R C.radius_pos s.ell s.ell_pos fstar))) : ℂ) =
      inner ℂ fstar
        (C.localBound.resolvent.stateResolvent (z + Complex.I * (s.tau : ℂ)) fstar) := by
  have hphi : C.parametrix.cutoffs.input.stateMul
      (placedWitness p R C.radius_pos s.ell s.ell_pos fstar) =
      placedWitness p R C.radius_pos s.ell s.ell_pos fstar :=
    inputMul_stateMul_placedWitness p R C.radius_pos s.ell s.ell_pos fstar hsupp C.box hfit
  have hrestrict : C.parametrix.selected.restrictInput
      (placedWitness p R C.radius_pos s.ell s.ell_pos fstar) =
      scaledWitness p s.ell s.ell_pos fstar :=
    restrictInputC2_placedWitness p R C.radius_pos s.ell s.ell_pos fstar hsupp C.box hfit
  have hstate : ∀ w : WholePlaneC2L2,
      (inner ℂ (placedWitness p R C.radius_pos s.ell s.ell_pos fstar)
        (C.parametrix.selected.extendState w) : ℂ) =
        inner ℂ (scaledWitness p s.ell s.ell_pos fstar) w := fun w ↦
    inner_placedWitness_extendStateC2 p R C.radius_pos s.ell s.ell_pos fstar hsupp C.box hfit w
  refine (inner_stateParametrix_eq_of_witness C.parametrix hphi hrestrict hstate z).trans ?_
  have hemb := embedding_scaledLocalResolventInv v p s C.localBound z
    (scaledWitness p s.ell s.ell_pos fstar)
  rw [C.parametrix_localEmbedding, C.parametrix_resolvent, hemb, rescale_symm_scaledWitness]
  exact (wholePlaneRescaleLinearIsometryEquiv C2 p s.ell s.ell_pos).inner_map_map fstar _

/-- **`eq:selected-contour-identity`** at the
selected cell: the normalized contour operator of `eq:Rapp`, tested against the placed witness
`f_n`, equals the local Riesz projection `P_{δ_n}` tested against the seed witness `f_*`. -/
theorem inner_contourOperator_placedWitness
    (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma) (fstar : WholePlaneC2L2)
    (hsupp : ∀ᵐ y ∂volume, Lstar < ‖y‖ → (fstar : WholePlane → C2) y = 0)
    (hfit : Lstar * s.ell ≤ R / 5) :
    (inner ℂ (placedWitness p R C.radius_pos s.ell s.ell_pos fstar)
        (contourOperator (horizontalInductionOperator u s.epsilon s.K)
          C.parametrix.approximateInverse (backgroundShiftedContour Gamma s.tau).center
          Gamma.radius (placedWitness p R C.radius_pos s.ell s.ell_pos fstar)) : ℂ) =
      inner ℂ fstar (C.localBound.resolvent.rieszProjection fstar) :=
  inner_contourOperator_eq_of_pointwise Gamma C.parametrix C.localBound.resolvent _ fstar
    fun z _ ↦ inner_stateParametrix_placedWitness C fstar hsupp hfit z

end CellWitness

end TorusSelectedContourIdentity

end

end FastDynamo

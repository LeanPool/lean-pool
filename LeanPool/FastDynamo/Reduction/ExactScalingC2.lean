/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.WholePlaneLocalC2
public import LeanPool.FastDynamo.Reduction.ExactScalingParameters

/-!
# Exact scaling of the two-component selected whole-plane operator

This module formalises `lem:exact-renormalization` of the paper for the **two-component**
operators of
`FastDynamo/Operator/WholePlaneLocalC2.lean`:

`U_n⁻¹ A^{(n)}_{ε,n} U_n = 𝓛_{δ_n} - iτ` as operators with domain `H²(ℝ²; ℂ²)`
(`eq:scaling`).

The unitary `U_n` displayed before the lemma is

`(U_n f)(y) = ℓ_n⁻¹ f((y - p_n)/ℓ_n)`,   `(U_n⁻¹ g)(Y) = ℓ_n g(p_n + ℓ_n Y)`,

realised twice, with different types: `wholePlaneRescaleLinearIsometryEquiv C2`
on `L²(ℝ²; ℂ²)` and `wholePlaneRescaleH2CLE C2` on the weak `H²` graph domain.  Both are the
fibre-generic maps of `FastDynamo/Analysis/WholePlane{Scaling,CoefficientScaling}.lean`, so the
two-component instance is free.

The scalar matching data is the record `WholePlaneExactScalingParameters` of
`FastDynamo/Reduction/ExactScalingParameters.lean`, reused verbatim: it stores
`δ = ε/ℓ²` (the choice of `n(ε)` in §5), `N = (2πK)ℓ` and `τ = (2πK)a`, which are the paper's
`2πK_n a_n = τ` and, with `N = 2π`, `K_nℓ_n = 1` (proof of the lemma).  The velocity copy
`u_n^loc(p_n + ℓ_nY) = ℓ_n v(Y)` (same proof) is the unnormalised coefficient pullback
`rescaledWholePlaneVelocityCoefficients`, also reused verbatim — the velocity coefficient
record is three-component and therefore fibre-independent.

**The stretching identity.**  The two-component stretching term carries the horizontal
projection `(∂_j v)⊥` of the derivative coefficients, so the exact scaling of that term needs
the commutation of `wholePlaneHorizontalProjLInf` with the coefficient pullback, and the
coordinate lemma `wholePlaneC2CoordL2_rescale`.  Both follow from two generic statements proved
here: a pointwise fibre map `L : F →L[ℂ] G` commutes with the normalised `L²` rescaling and with
the unnormalised `L∞` coefficient pullback.

The contour consequence stated after the lemma (`Γ_τ = {z - iτ : z ∈ Γ}`, real parts
unchanged) is pure scalar geometry and is not repeated here; the eigenpair and pencil
translations proved below are what `cor:scaled-local-resolvents`
(`R_n = U_n (· + iτ - 𝓛_{δ_n})⁻¹ U_n⁻¹`, its proof) consumes.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

/-! ## A pointwise fibre map commutes with both affine transports -/

section FibreMap

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The normalised affine `L²` rescaling as a linear map acts by the plain rescaling.  This
`rfl` lemma is what lets the termwise conjugation identities be closed by `simp only`, without
a defeq check between the bundled and unbundled forms on large terms. -/
theorem wholePlaneRescaleLinear_apply (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell) (f : WholePlaneL2 F) :
    wholePlaneRescaleLinear F p ell hell f = wholePlaneRescale F p ell hell f :=
  rfl

/-- A pointwise fibre map commutes with the normalised affine `L²` rescaling `U_{p,ℓ}`. -/
theorem compLpL_wholePlaneRescale (L : F →L[ℂ] G)
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell) (f : WholePlaneL2 F) :
    L.compLpL 2 volume (wholePlaneRescale F p ell hell f) =
      wholePlaneRescale G p ell hell (L.compLpL 2 volume f) := by
  apply Lp.ext
  have hbasePull :=
    (measurePreserving_wholePlaneAffine p ell hell).quasiMeasurePreserving.ae_eq_comp
      (Measure.ae_smul_measure
        (L.coeFn_compLpL (p := 2) (μ := (volume : Measure WholePlane)) f)
        (ENNReal.ofReal (ell ^ 2)))
  filter_upwards [L.coeFn_compLpL (wholePlaneRescale F p ell hell f),
    wholePlaneRescale_coe_ae F p ell hell f,
    wholePlaneRescale_coe_ae G p ell hell (L.compLpL 2 volume f),
    hbasePull] with y hl hv hr hb
  have hb' :
      ((L.compLpL 2 volume f : WholePlaneL2 G) : WholePlane → G)
          (wholePlaneAffine p ell y) =
        L (f (wholePlaneAffine p ell y)) := by
    simpa only [Function.comp_apply] using hb
  rw [hl, hv, hr, hb', map_smul]

/-- A pointwise fibre map commutes with the unnormalised affine `L∞` coefficient pullback. -/
theorem compLpL_wholePlaneCoeffPullback (L : F →L[ℂ] G)
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell) (a : WholePlaneLInf F) :
    L.compLpL ∞ volume (wholePlaneCoeffPullback F p ell hell a) =
      wholePlaneCoeffPullback G p ell hell (L.compLpL ∞ volume a) := by
  apply Lp.ext
  have hbasePull :=
    (measurePreserving_wholePlaneAffine p ell hell).quasiMeasurePreserving.ae_eq_comp
      (Measure.ae_smul_measure
        (L.coeFn_compLpL (p := ∞) (μ := (volume : Measure WholePlane)) a)
        (ENNReal.ofReal (ell ^ 2)))
  filter_upwards [L.coeFn_compLpL (wholePlaneCoeffPullback F p ell hell a),
    wholePlaneCoeffPullback_coe_ae F p ell hell a,
    wholePlaneCoeffPullback_coe_ae G p ell hell (L.compLpL ∞ volume a),
    hbasePull] with y hl hv hr hb
  have hb' :
      ((L.compLpL ∞ volume a : WholePlaneLInf G) : WholePlane → G)
          (wholePlaneAffine p ell y) =
        L (a (wholePlaneAffine p ell y)) := by
    simpa only [Function.comp_apply] using hb
  rw [hl, hv, hr, hb']

end FibreMap

/-! ## The two two-component coefficient compatibilities -/

/-- Coordinate projection on two-component fields commutes exactly with the normalised `L²`
rescaling. -/
theorem wholePlaneC2CoordL2_rescale (j : Fin 2)
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell) (v : WholePlaneC2L2) :
    wholePlaneC2CoordL2 j (wholePlaneRescale C2 p ell hell v) =
      wholePlaneRescale ℂ p ell hell (wholePlaneC2CoordL2 j v) :=
  compLpL_wholePlaneRescale (EuclideanSpace.proj j) p ell hell v

/-- The horizontal projection of velocity gradient coefficients commutes exactly with the
unnormalised coefficient pullback. -/
theorem wholePlaneHorizontalProjLInf_coeffPullback
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell) (a : WholePlaneC3LInf) :
    wholePlaneHorizontalProjLInf (wholePlaneCoeffPullback C3 p ell hell a) =
      wholePlaneCoeffPullback C2 p ell hell (wholePlaneHorizontalProjLInf a) :=
  compLpL_wholePlaneCoeffPullback horizontalProjPoint p ell hell a

/-- One scalar coordinate of the rescaled velocity value is `ell` times the affine pullback of
the corresponding coordinate of `v`; coordinate extraction commutes with the pullback. -/
theorem wholePlaneCoordLInf_rescaledVelocityValue
    (v : WholePlaneVelocityCoefficients) (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (i : Fin 3) :
    wholePlaneCoordLInf i (rescaledWholePlaneVelocityCoefficients v p ell hell).value =
      (ell : ℂ) • wholePlaneCoeffPullback ℂ p ell hell (wholePlaneCoordLInf i v.value) := by
  change wholePlaneCoordLInf i
      ((ell : ℂ) • wholePlaneCoeffPullback C3 p ell hell v.value) = _
  rw [map_smul, wholePlaneCoordLInf_coeffPullback]

/-- The horizontal gradient coefficients of the rescaled local velocity are the plain affine
pullbacks of the horizontal gradient coefficients of `v`, with no extra factor of `ell`. -/
theorem horizontalDeriv_rescaledWholePlaneVelocityCoefficients
    (v : WholePlaneVelocityCoefficients) (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (j : Fin 2) :
    (rescaledWholePlaneVelocityCoefficients v p ell hell).horizontalDeriv j =
      wholePlaneCoeffPullback C2 p ell hell (v.horizontalDeriv j) := by
  change wholePlaneHorizontalProjLInf
      (wholePlaneCoeffPullback C3 p ell hell (v.deriv j)) = _
  rw [wholePlaneHorizontalProjLInf_coeffPullback]
  rfl

/-! ## The vertically shifted two-component local operator -/

/-- The two-component local action after the constant axial spectral translation:
`𝓛_δ - iτ` (`eq:scaling`). -/
def shiftedWholePlaneC2LocalAction
    (v : WholePlaneVelocityCoefficients) (delta N tau : ℝ) :
    WholePlaneC2H2 →L[ℂ] WholePlaneC2L2 :=
  wholePlaneC2LocalAction v delta N -
    (Complex.I * (tau : ℂ)) • wholePlaneH2Embedding C2

/-- The domain-aware realisation of `𝓛_δ - iτ` on `L²(ℝ²; ℂ²)` with domain
`H²(ℝ²; ℂ²)` (`lem:exact-renormalization`). -/
def shiftedWholePlaneC2LocalOperator
    (v : WholePlaneVelocityCoefficients) (delta N tau : ℝ) :
    DomainOperator WholePlaneC2L2 WholePlaneC2H2 where
  embedding := wholePlaneH2Embedding C2
  embedding_injective := wholePlaneH2Embedding_injective C2
  op := shiftedWholePlaneC2LocalAction v delta N tau

/-! ## Exact termwise conjugation -/

section Terms

variable (v : WholePlaneVelocityCoefficients)
  (p : WholePlane) (s : WholePlaneExactScalingParameters)

/-- Abbreviation for the rescaled local velocity copy `u_n^loc(y) = ℓ v((y - p)/ℓ)` used
throughout the termwise conjugation computations. -/
abbrev uLocScaled : WholePlaneVelocityCoefficients :=
  rescaledWholePlaneVelocityCoefficients v p s.ell s.ell_pos

/-- Abbreviation for the normalised affine rescaling `U_n` as a linear isometry of the
two-component whole-plane `L²`. -/
abbrev rescaleState : WholePlaneC2L2 ≃ₗᵢ[ℂ] WholePlaneC2L2 :=
  wholePlaneRescaleLinearIsometryEquiv C2 p s.ell s.ell_pos

/-- Abbreviation for the normalised affine rescaling `U_n` acting on the two-component
whole-plane weak `H²` graph domain. -/
abbrev rescaleDomain : WholePlaneC2H2 ≃L[ℂ] WholePlaneC2H2 :=
  wholePlaneRescaleH2CLE C2 p s.ell s.ell_pos

/-- First term of the display in the proof of `lem:exact-renormalization`: diffusion and the fixed
axial Laplacian mass conjugate with `δ = ε/ℓ²` and `N = (2πK)ℓ`. -/
theorem exactScalingC2_diffusion (b : WholePlaneC2H2) :
    (s.epsilon : ℂ) •
        wholePlaneC2LocalDiffusion (wholePlaneAxialWavenumber s.K)
          (rescaleDomain p s b) =
      rescaleState p s ((s.delta : ℂ) • wholePlaneC2LocalDiffusion s.N b) := by
  change (s.epsilon : ℂ) •
      wholePlaneC2LocalDiffusion (wholePlaneAxialWavenumber s.K)
        (wholePlaneRescaleH2 C2 p s.ell s.ell_pos b) =
    (wholePlaneRescaleLinear C2 p s.ell s.ell_pos)
      ((s.delta : ℂ) • wholePlaneC2LocalDiffusion s.N b)
  rw [wholePlaneC2LocalDiffusion_apply, wholePlaneC2LocalDiffusion_apply,
    wholePlaneLaplacian_rescaleH2, wholePlaneH2Embedding_rescaleH2]
  simp only [map_smul, map_sub, smul_sub, smul_smul]
  rw [s.epsilon_mul_inv_ell_sq, s.epsilon_mul_physicalWave_sq]
  rfl

/-- Second term of the display in the proof of `lem:exact-renormalization`: transverse transport is
unchanged by the normalised cell conjugation. -/
theorem exactScalingC2_transverseTransport (b : WholePlaneC2H2) :
    wholePlaneC2LocalTransport (uLocScaled v p s) (rescaleDomain p s b) =
      rescaleState p s (wholePlaneC2LocalTransport v b) := by
  change wholePlaneC2LocalTransport (uLocScaled v p s)
      (wholePlaneRescaleH2 C2 p s.ell s.ell_pos b) =
    (wholePlaneRescaleLinear C2 p s.ell s.ell_pos)
      (wholePlaneC2LocalTransport v b)
  rw [wholePlaneC2LocalTransport_apply, wholePlaneC2LocalTransport_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [wholePlaneCoordLInf_rescaledVelocityValue, wholePlaneH2FirstDerivative_rescaleH2]
  simp only [map_smul, smul_apply, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr s.ell_ne_zero), one_smul]
  exact scalarVectorMulL2_coeffPullback_rescale C2 p s.ell s.ell_pos _ _

/-- Third term of the display in the proof of `lem:exact-renormalization`: the local axial transport
coefficient changes from `i(2πK)` to `iN`. -/
theorem exactScalingC2_localAxialTransport (b : WholePlaneC2H2) :
    wholePlaneC2LocalAxialTransport (uLocScaled v p s)
        (wholePlaneAxialWavenumber s.K) (rescaleDomain p s b) =
      rescaleState p s (wholePlaneC2LocalAxialTransport v s.N b) := by
  change wholePlaneC2LocalAxialTransport (uLocScaled v p s)
      (wholePlaneAxialWavenumber s.K)
        (wholePlaneRescaleH2 C2 p s.ell s.ell_pos b) =
    (wholePlaneRescaleLinear C2 p s.ell s.ell_pos)
      (wholePlaneC2LocalAxialTransport v s.N b)
  rw [wholePlaneC2LocalAxialTransport_apply, wholePlaneC2LocalAxialTransport_apply,
    wholePlaneCoordLInf_rescaledVelocityValue, wholePlaneH2Embedding_rescaleH2]
  simp only [map_smul, smul_apply, smul_smul]
  simp only [scalarVectorMulL2_coeffPullback_rescale, s.physicalWave_mul_ell,
    wholePlaneRescaleLinear_apply]

/-- Fourth term of the display in the proof of `lem:exact-renormalization`: stretching by the
horizontal gradient of the local copy conjugates without an additional length factor. -/
theorem exactScalingC2_stretching (b : WholePlaneC2H2) :
    wholePlaneC2LocalStretching (uLocScaled v p s) (rescaleDomain p s b) =
      rescaleState p s (wholePlaneC2LocalStretching v b) := by
  change wholePlaneC2LocalStretching (uLocScaled v p s)
      (wholePlaneRescaleH2 C2 p s.ell s.ell_pos b) =
    (wholePlaneRescaleLinear C2 p s.ell s.ell_pos)
      (wholePlaneC2LocalStretching v b)
  rw [wholePlaneC2LocalStretching_apply, wholePlaneC2LocalStretching_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [horizontalDeriv_rescaledWholePlaneVelocityCoefficients,
    wholePlaneH2Embedding_rescaleH2, wholePlaneC2CoordL2_rescale,
    vectorScalarMulL2_coeffPullback_rescale, wholePlaneRescaleLinear_apply]

/-- Fifth term of the display in the proof of `lem:exact-renormalization`: the constant axial
velocity is exactly the scalar translation `iτ`, because `2πK a = τ`.  The minus sign is
introduced when this term is subtracted in the selected action. -/
theorem exactScalingC2_constantAxialShift (b : WholePlaneC2H2) :
    selectedWholePlaneC2AxialShift s.K s.a (rescaleDomain p s b) =
      rescaleState p s ((Complex.I * (s.tau : ℂ)) • wholePlaneH2Embedding C2 b) := by
  change selectedWholePlaneC2AxialShift s.K s.a
      (wholePlaneRescaleH2 C2 p s.ell s.ell_pos b) =
    (wholePlaneRescaleLinear C2 p s.ell s.ell_pos)
      ((Complex.I * (s.tau : ℂ)) • wholePlaneH2Embedding C2 b)
  rw [selectedWholePlaneC2AxialShift_apply, wholePlaneH2Embedding_rescaleH2, map_smul,
    s.axialShift_eq]
  rfl

/-- The first four termwise identities assemble to the conjugation of the selected local-copy
action before the constant axial shift is subtracted. -/
theorem exactScalingC2_localAction (b : WholePlaneC2H2) :
    wholePlaneC2LocalAction (uLocScaled v p s) s.epsilon
        (wholePlaneAxialWavenumber s.K) (rescaleDomain p s b) =
      rescaleState p s (wholePlaneC2LocalAction v s.delta s.N b) := by
  have hdiff := exactScalingC2_diffusion p s b
  have htransport := exactScalingC2_transverseTransport v p s b
  have haxial := exactScalingC2_localAxialTransport v p s b
  have hstretch := exactScalingC2_stretching v p s b
  simp only [wholePlaneC2LocalAction, add_apply, sub_apply, smul_apply,
    map_add, map_sub, map_smul, hdiff, htransport, haxial, hstretch]

/-- Complete forward intertwining in `lem:exact-renormalization`, including the
fifth term: the selected whole-plane action is the normalised rescaling of `𝓛_δ - iτ`. -/
theorem exactScalingC2_selectedAction (b : WholePlaneC2H2) :
    selectedWholePlaneC2InductionAction (uLocScaled v p s)
        s.epsilon s.K s.a (rescaleDomain p s b) =
      rescaleState p s (shiftedWholePlaneC2LocalAction v s.delta s.N s.tau b) := by
  have hlocal := exactScalingC2_localAction v p s b
  have hshift := exactScalingC2_constantAxialShift p s b
  simp only [selectedWholePlaneC2InductionAction, shiftedWholePlaneC2LocalAction,
    sub_apply, smul_apply, map_sub, hlocal, hshift]

/-- Conjugated form of `eq:scaling`:
`U_n⁻¹ A^{(n)}_{ε,n} U_n = 𝓛_{δ_n} - iτ`. -/
theorem exactScalingC2_selectedAction_conjugated (b : WholePlaneC2H2) :
    (rescaleState p s).symm
        (selectedWholePlaneC2InductionAction (uLocScaled v p s)
          s.epsilon s.K s.a (rescaleDomain p s b)) =
      shiftedWholePlaneC2LocalAction v s.delta s.N s.tau b := by
  rw [exactScalingC2_selectedAction]
  exact (rescaleState p s).symm_apply_apply _

/-- `eq:scaling` as an equality of bounded maps from the `H²` graph domain to `L²`: the
conjugated selected whole-plane action **is** the shifted local action. -/
theorem exactScalingC2_selectedAction_clm :
    (rescaleState p s).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((selectedWholePlaneC2InductionAction (uLocScaled v p s)
          s.epsilon s.K s.a).comp (rescaleDomain p s).toContinuousLinearMap) =
      shiftedWholePlaneC2LocalAction v s.delta s.N s.tau := by
  apply ContinuousLinearMap.ext
  intro b
  exact exactScalingC2_selectedAction_conjugated v p s b

/-- The domain embedding is conjugated by the same, separately typed, `H²`- and
`L²`-rescaling maps. -/
theorem exactScalingC2_embedding (b : WholePlaneC2H2) :
    wholePlaneH2Embedding C2 (rescaleDomain p s b) =
      rescaleState p s (wholePlaneH2Embedding C2 b) := by
  change wholePlaneH2Embedding C2
      (wholePlaneRescaleH2 C2 p s.ell s.ell_pos b) =
    wholePlaneRescaleLinear C2 p s.ell s.ell_pos
      (wholePlaneH2Embedding C2 b)
  rw [wholePlaneH2Embedding_rescaleH2]
  rfl

/-- Conjugated form of the domain-embedding identity. -/
theorem exactScalingC2_embedding_conjugated (b : WholePlaneC2H2) :
    (rescaleState p s).symm (wholePlaneH2Embedding C2 (rescaleDomain p s b)) =
      wholePlaneH2Embedding C2 b := by
  rw [exactScalingC2_embedding]
  exact (rescaleState p s).symm_apply_apply _

/-- Operator-field version of the exact action conjugation. -/
theorem exactScalingC2_selectedOperator_action_conjugated (b : WholePlaneC2H2) :
    (rescaleState p s).symm
        ((selectedWholePlaneC2InductionOperator (uLocScaled v p s)
          s.epsilon s.K s.a).op (rescaleDomain p s b)) =
      (shiftedWholePlaneC2LocalOperator v s.delta s.N s.tau).op b :=
  exactScalingC2_selectedAction_conjugated v p s b

/-- Operator-field version of the domain-embedding conjugation. -/
theorem exactScalingC2_selectedOperator_embedding_conjugated (b : WholePlaneC2H2) :
    (rescaleState p s).symm
        ((selectedWholePlaneC2InductionOperator (uLocScaled v p s)
          s.epsilon s.K s.a).embedding (rescaleDomain p s b)) =
      (shiftedWholePlaneC2LocalOperator v s.delta s.N s.tau).embedding b :=
  exactScalingC2_embedding_conjugated p s b

/-- Conjugating the selected whole-plane pencil gives the pencil of the shifted local operator
at the same spectral parameter. -/
theorem exactScalingC2_selectedOperator_pencil_conjugated
    (z : ℂ) (b : WholePlaneC2H2) :
    (rescaleState p s).symm
        ((selectedWholePlaneC2InductionOperator (uLocScaled v p s)
          s.epsilon s.K s.a).pencil z (rescaleDomain p s b)) =
      (shiftedWholePlaneC2LocalOperator v s.delta s.N s.tau).pencil z b := by
  change (rescaleState p s).symm
      (z • wholePlaneH2Embedding C2 (rescaleDomain p s b) -
        selectedWholePlaneC2InductionAction (uLocScaled v p s)
          s.epsilon s.K s.a (rescaleDomain p s b)) =
    z • wholePlaneH2Embedding C2 b -
      shiftedWholePlaneC2LocalAction v s.delta s.N s.tau b
  rw [map_sub, map_smul, exactScalingC2_embedding_conjugated,
    exactScalingC2_selectedAction_conjugated]

/-- Subtracting `iτ` from the local action translates its pencil by `z ↦ z + iτ`. -/
theorem shiftedWholePlaneC2LocalOperator_pencil_eq (z : ℂ) (b : WholePlaneC2H2) :
    (shiftedWholePlaneC2LocalOperator v s.delta s.N s.tau).pencil z b =
      (wholePlaneC2LocalOperator v s.delta s.N).pencil
        (z + Complex.I * (s.tau : ℂ)) b := by
  change z • wholePlaneH2Embedding C2 b -
      (wholePlaneC2LocalAction v s.delta s.N b -
        (Complex.I * (s.tau : ℂ)) • wholePlaneH2Embedding C2 b) =
    (z + Complex.I * (s.tau : ℂ)) • wholePlaneH2Embedding C2 b -
      wholePlaneC2LocalAction v s.delta s.N b
  rw [add_smul]
  module

/-- Pencil translation under exact cell rescaling: the conjugated selected pencil
at `z` is the local pencil at `z + iτ`. -/
theorem exactScalingC2_pencil_translation (z : ℂ) (b : WholePlaneC2H2) :
    (rescaleState p s).symm
        ((selectedWholePlaneC2InductionOperator (uLocScaled v p s)
          s.epsilon s.K s.a).pencil z (rescaleDomain p s b)) =
      (wholePlaneC2LocalOperator v s.delta s.N).pencil
        (z + Complex.I * (s.tau : ℂ)) b := by
  rw [exactScalingC2_selectedOperator_pencil_conjugated,
    shiftedWholePlaneC2LocalOperator_pencil_eq]

/-! ## Eigenpair translation -/

/-- An eigenpair of `𝓛_δ - iτ` at `λ` is exactly an eigenpair of `𝓛_δ` at `λ + iτ`. -/
theorem shiftedWholePlaneC2LocalOperator_isEigenpair_iff
    (lambda : ℂ) (b : WholePlaneC2H2) :
    (shiftedWholePlaneC2LocalOperator v s.delta s.N s.tau).IsEigenpair lambda b ↔
      (wholePlaneC2LocalOperator v s.delta s.N).IsEigenpair
        (lambda + Complex.I * (s.tau : ℂ)) b := by
  constructor
  · rintro ⟨hnonzero, heigen⟩
    refine ⟨hnonzero, ?_⟩
    change wholePlaneC2LocalAction v s.delta s.N b =
      (lambda + Complex.I * (s.tau : ℂ)) • wholePlaneH2Embedding C2 b
    change wholePlaneC2LocalAction v s.delta s.N b -
        (Complex.I * (s.tau : ℂ)) • wholePlaneH2Embedding C2 b =
      lambda • wholePlaneH2Embedding C2 b at heigen
    rw [add_smul]
    exact sub_eq_iff_eq_add.mp heigen
  · rintro ⟨hnonzero, heigen⟩
    refine ⟨hnonzero, ?_⟩
    change wholePlaneC2LocalAction v s.delta s.N b -
        (Complex.I * (s.tau : ℂ)) • wholePlaneH2Embedding C2 b =
      lambda • wholePlaneH2Embedding C2 b
    apply sub_eq_iff_eq_add.mpr
    rw [← add_smul]
    exact heigen

/-- Exact rescaling preserves the eigenpair condition between the selected whole-plane operator
and the shifted local operator.  The nonzero clause is transported through the injective `L²`
isometry, not inferred pointwise. -/
theorem exactScalingC2_selectedOperator_isEigenpair_iff_shifted
    (lambda : ℂ) (b : WholePlaneC2H2) :
    (selectedWholePlaneC2InductionOperator (uLocScaled v p s)
        s.epsilon s.K s.a).IsEigenpair lambda (rescaleDomain p s b) ↔
      (shiftedWholePlaneC2LocalOperator v s.delta s.N s.tau).IsEigenpair lambda b := by
  constructor
  · rintro ⟨hnonzero, heigen⟩
    constructor
    · intro hzero
      apply hnonzero
      apply (rescaleState p s).symm.injective
      rw [exactScalingC2_selectedOperator_embedding_conjugated, map_zero, hzero]
    · have hconjugated := congrArg (rescaleState p s).symm heigen
      rw [exactScalingC2_selectedOperator_action_conjugated, map_smul,
        exactScalingC2_selectedOperator_embedding_conjugated] at hconjugated
      exact hconjugated
  · rintro ⟨hnonzero, heigen⟩
    constructor
    · intro hzero
      apply hnonzero
      have hconjugated := congrArg (rescaleState p s).symm hzero
      rw [exactScalingC2_selectedOperator_embedding_conjugated, map_zero] at hconjugated
      exact hconjugated
    · apply (rescaleState p s).symm.injective
      rw [exactScalingC2_selectedOperator_action_conjugated, map_smul,
        exactScalingC2_selectedOperator_embedding_conjugated, heigen]

/-- Full eigenpair translation in `lem:exact-renormalization`:
`A^{(n)}_{ε,n}(U_n f) = λ(U_n f)` exactly when `𝓛_{δ_n} f = (λ + iτ)f`. -/
theorem exactScalingC2_eigenpair_iff (lambda : ℂ) (b : WholePlaneC2H2) :
    (selectedWholePlaneC2InductionOperator (uLocScaled v p s)
        s.epsilon s.K s.a).IsEigenpair lambda (rescaleDomain p s b) ↔
      (wholePlaneC2LocalOperator v s.delta s.N).IsEigenpair
        (lambda + Complex.I * (s.tau : ℂ)) b := by
  rw [exactScalingC2_selectedOperator_isEigenpair_iff_shifted,
    shiftedWholePlaneC2LocalOperator_isEigenpair_iff]

/-- Converse paper direction: a selected-cell eigenvalue `μ` becomes the local eigenvalue
`μ + iτ`. -/
theorem exactScalingC2_selectedEigenpair_to_local
    (mu : ℂ) (b : WholePlaneC2H2)
    (h : (selectedWholePlaneC2InductionOperator (uLocScaled v p s)
      s.epsilon s.K s.a).IsEigenpair mu (rescaleDomain p s b)) :
    (wholePlaneC2LocalOperator v s.delta s.N).IsEigenpair
      (mu + Complex.I * (s.tau : ℂ)) b :=
  (exactScalingC2_eigenpair_iff v p s mu b).1 h

end Terms

end

end FastDynamo

/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Conventions
public import Mathlib.Analysis.Distribution.Sobolev

/-!
# Whole-plane `L²`, Plancherel Fourier analysis, and physical momentum

The local instability of `prop:local-seed` (Proposition 2.2) acts on fields over `ℝ²`.  This
file fixes that physical space, exposes Mathlib's Plancherel transform as a bundled linear
isometry, and proves compatibility with the canonical embedding into tempered distributions.

Mathlib uses the Fourier character `exp (-2π i inner ξ y)`, while the
paper's multiplier formulas use the corresponding angular (physical)
momentum.  Thus a momentum `p` in the paper normalization corresponds to
`p = 2π ξ` in Mathlib's normalized coordinates.  The last theorem records
this conversion in the coordinate derivative symbol.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped FourierTransform LineDeriv SchwartzMap

/-- The transverse whole plane used by the local model. -/
abbrev WholePlane := EuclideanSpace ℝ (Fin 2)

/-- Generic normed-group-valued `L²` on the transverse whole plane. -/
abbrev WholePlaneL2 (F : Type*) [NormedAddCommGroup F] :=
  Lp F 2 (volume : Measure WholePlane)

/-- Scalar complex `L²(ℝ²)`. -/
abbrev WholePlaneScalarL2 := WholePlaneL2 ℂ

/-- Three-component complex `L²(ℝ²)`. -/
abbrev WholePlaneC3L2 := WholePlaneL2 C3

/-- The `j`-th coordinate vector in the transverse whole plane. -/
def wholePlaneBasis (j : Fin 2) : WholePlane :=
  EuclideanSpace.single j 1

/-- Pairing with the `j`th coordinate vector reads off the `j`th coordinate:
`⟪ξ, e_j⟫ = ξ j`. -/
@[simp] theorem inner_wholePlaneBasis (ξ : WholePlane) (j : Fin 2) :
    inner ℝ ξ (wholePlaneBasis j) = ξ j := by
  simpa [wholePlaneBasis] using
    (EuclideanSpace.inner_single_right j (1 : ℝ) ξ)

/-- Physical momentum corresponding to Mathlib's normalized Fourier variable. -/
def wholePlaneMomentum (ξ : WholePlane) : WholePlane :=
  (2 * Real.pi) • ξ

/-- The physical momentum has coordinates `2π ξ_j`, which is the conversion between
Mathlib's normalized Fourier variable and the paper's momentum. -/
@[simp] theorem wholePlaneMomentum_apply (ξ : WholePlane) (j : Fin 2) :
    wholePlaneMomentum ξ j = 2 * Real.pi * ξ j := by
  simp [wholePlaneMomentum]

section Fourier

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Plancherel Fourier analysis on Hilbert-valued `L²(ℝ²)`. -/
def wholePlaneFourierAnalysis :
    WholePlaneL2 F ≃ₗᵢ[ℂ] WholePlaneL2 F :=
  Lp.fourierTransformₗᵢ WholePlane F

/-- Inverse Fourier synthesis on Hilbert-valued `L²(ℝ²)`. -/
def wholePlaneFourierSynthesis :
    WholePlaneL2 F ≃ₗᵢ[ℂ] WholePlaneL2 F :=
  (wholePlaneFourierAnalysis F).symm

/-- The bundled analysis isometry is Mathlib's `L²` Fourier transform `𝓕`. -/
@[simp] theorem wholePlaneFourierAnalysis_apply (f : WholePlaneL2 F) :
    wholePlaneFourierAnalysis F f = 𝓕 f :=
  rfl

/-- The bundled synthesis isometry is Mathlib's inverse `L²` Fourier transform `𝓕⁻`. -/
@[simp] theorem wholePlaneFourierSynthesis_apply (f : WholePlaneL2 F) :
    wholePlaneFourierSynthesis F f = 𝓕⁻ f :=
  rfl

/-- Analysis undoes synthesis on whole-plane `L²`. -/
theorem wholePlaneFourierAnalysis_synthesis (f : WholePlaneL2 F) :
    wholePlaneFourierAnalysis F (wholePlaneFourierSynthesis F f) = f :=
  (wholePlaneFourierAnalysis F).apply_symm_apply f

/-- Synthesis undoes analysis on whole-plane `L²`. -/
theorem wholePlaneFourierSynthesis_analysis (f : WholePlaneL2 F) :
    wholePlaneFourierSynthesis F (wholePlaneFourierAnalysis F f) = f :=
  (wholePlaneFourierAnalysis F).symm_apply_apply f

/-- Parseval: Fourier analysis preserves the `L²` inner product. -/
theorem inner_wholePlaneFourierAnalysis (f g : WholePlaneL2 F) :
    inner ℂ (wholePlaneFourierAnalysis F f) (wholePlaneFourierAnalysis F g) =
      inner ℂ f g :=
  (wholePlaneFourierAnalysis F).inner_map_map f g

/-- Canonical continuous embedding of whole-plane `L²` into tempered
distributions. -/
def wholePlaneL2ToTempered :
    WholePlaneL2 F →L[ℂ] 𝓢'(WholePlane, F) :=
  Lp.toTemperedDistributionCLM F volume 2

/-- Distinct `L²` classes represent distinct tempered distributions, so no information is
lost when passing to the distributional model. -/
theorem wholePlaneL2ToTempered_injective :
    Function.Injective (wholePlaneL2ToTempered F) := by
  apply LinearMap.ker_eq_bot.mp
  exact Lp.ker_toTemperedDistributionCLM_eq_bot

/-- The embedding into tempered distributions is the canonical coercion of an `L²`
class. -/
@[simp] theorem wholePlaneL2ToTempered_apply (f : WholePlaneL2 F) :
    wholePlaneL2ToTempered F f = (f : 𝓢'(WholePlane, F)) :=
  rfl

/-- Compatibility of the Plancherel `L²` transform with the distributional
Fourier transform. This wrapper fixes both embeddings explicitly, so later
unbounded-multiplier theorems cannot accidentally mix the two Fourier APIs. -/
theorem fourier_wholePlaneL2ToTempered (f : WholePlaneL2 F) :
    𝓕 (wholePlaneL2ToTempered F f) =
      wholePlaneL2ToTempered F (wholePlaneFourierAnalysis F f) := by
  simpa only [wholePlaneL2ToTempered_apply, wholePlaneFourierAnalysis_apply] using
    (Lp.fourier_toTemperedDistribution_eq f)

/-- Compatibility of inverse Plancherel synthesis with inverse Fourier
transform on tempered distributions. -/
theorem fourierInv_wholePlaneL2ToTempered (f : WholePlaneL2 F) :
    𝓕⁻ (wholePlaneL2ToTempered F f) =
      wholePlaneL2ToTempered F (wholePlaneFourierSynthesis F f) := by
  simpa only [wholePlaneL2ToTempered_apply, wholePlaneFourierSynthesis_apply] using
    (Lp.fourierInv_toTemperedDistribution_eq f)

omit [CompleteSpace F] in
/-- Coordinate weak differentiation has the physical-momentum symbol
`i p_j`, where `p = 2π ξ` converts Mathlib's Fourier variable to the
paper's momentum convention. -/
theorem fourier_lineDeriv_wholePlaneBasis_eq_momentum
    (f : 𝓢'(WholePlane, F)) (j : Fin 2) :
    𝓕 (∂_{wholePlaneBasis j} f) =
      TemperedDistribution.smulLeftCLM F
        (fun ξ : WholePlane => Complex.I * wholePlaneMomentum ξ j)
        (𝓕 f) := by
  rw [TemperedDistribution.fourier_lineDerivOp_eq]
  change ((2 * Real.pi * Complex.I) •
      TemperedDistribution.smulLeftCLM F
        (fun ξ : WholePlane => ((inner ℝ ξ (wholePlaneBasis j) : ℝ) : ℂ)))
      (𝓕 f) = _
  rw [← TemperedDistribution.smulLeftCLM_smul (by fun_prop)
    (2 * Real.pi * Complex.I)]
  congr 2
  funext ξ
  simp [Pi.smul_apply, inner_wholePlaneBasis, wholePlaneMomentum_apply]
  ring

/-- Multiplication of an `L²` representative by a temperate scalar symbol
commutes with the canonical embedding into tempered distributions.  The
statement is phrased using an arbitrary a.e.-equal output, which is the form
needed for quotient-level `L²` multipliers. -/
theorem smulLeftCLM_wholePlaneL2ToTempered_eq_of_ae
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F]
    (g : WholePlane → ℂ) (hg : g.HasTemperateGrowth)
    (u v : WholePlaneL2 F)
    (h : (v : WholePlane → F) =ᵐ[volume]
      fun xi => g xi • (u xi : F)) :
    TemperedDistribution.smulLeftCLM F g
        (wholePlaneL2ToTempered F u) =
      wholePlaneL2ToTempered F v := by
  ext f
  simp only [TemperedDistribution.smulLeftCLM_apply_apply,
    wholePlaneL2ToTempered_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h] with xi hxi
  rw [hxi]
  simp [SchwartzMap.smulLeftCLM_apply_apply, hg, smul_smul, mul_comm]

end Fourier

namespace WholePlaneHorizontalFibre

variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- A bounded fibre map acting pointwise on whole-plane `L²` fields. -/
def fibreL2 (L : F →L[ℂ] G) : WholePlaneL2 F →L[ℂ] WholePlaneL2 G :=
  L.compLpL 2 volume

omit [CompleteSpace F] [CompleteSpace G] in
/-- The pointwise fibre action is represented almost everywhere by the pointwise image. -/
theorem fibreL2_coe_ae (L : F →L[ℂ] G) (f : WholePlaneL2 F) :
    (fibreL2 L f : WholePlane → G) =ᵐ[volume] fun x ↦ L ((f : WholePlane → F) x) :=
  L.coeFn_compLpL f

/-- A bounded fibre map acting on whole-plane tempered distributions by postcomposition. -/
def fibreTempered (L : F →L[ℂ] G) :
    TemperedDistribution WholePlane F →L[ℂ] TemperedDistribution WholePlane G :=
  PointwiseConvergenceCLM.postcomp (SchwartzMap WholePlane ℂ) L

omit [CompleteSpace F] [CompleteSpace G] in
/-- Postcomposition acts after testing. -/
@[simp] theorem fibreTempered_apply_apply (L : F →L[ℂ] G)
    (T : TemperedDistribution WholePlane F) (phi : SchwartzMap WholePlane ℂ) :
    fibreTempered L T phi = L (T phi) :=
  rfl

omit [CompleteSpace F] [CompleteSpace G] in
/-- Postcomposition commutes with distributional line differentiation. -/
theorem fibreTempered_lineDeriv (L : F →L[ℂ] G) (e : WholePlane)
    (T : TemperedDistribution WholePlane F) :
    fibreTempered L (∂_{e} T) = ∂_{e} (fibreTempered L T) := by
  ext phi
  rfl

/-- The canonical `L² → 𝓢'` embedding commutes with a bounded fibre map. -/
theorem fibreTempered_l2 (L : F →L[ℂ] G) (f : WholePlaneL2 F) :
    fibreTempered L (wholePlaneL2ToTempered F f) =
      wholePlaneL2ToTempered G (fibreL2 L f) := by
  apply ContinuousLinearMap.ext
  intro phi
  have hint : Integrable (fun x : WholePlane ↦ phi x • ((f : WholePlane → F) x)) volume :=
    memLp_one_iff_integrable.mp <|
      (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] F →L[ℂ] F).memLp_of_bilin
        1 (phi.memLp 2 volume) (Lp.memLp f)
  calc
    fibreTempered L (wholePlaneL2ToTempered F f) phi =
        L ((wholePlaneL2ToTempered F f) phi) := rfl
    _ = L (∫ x : WholePlane, phi x • ((f : WholePlane → F) x) ∂volume) := by
      rw [wholePlaneL2ToTempered_apply, MeasureTheory.Lp.toTemperedDistribution_apply]
    _ = ∫ x : WholePlane, L (phi x • ((f : WholePlane → F) x)) ∂volume :=
      (L.integral_comp_comm hint).symm
    _ = ∫ x : WholePlane, phi x • ((fibreL2 L f : WholePlane → G) x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [fibreL2_coe_ae L f] with x hx
      rw [hx]
      exact L.map_smul_of_tower (phi x) _
    _ = (wholePlaneL2ToTempered G (fibreL2 L f)) phi := by
      rw [wholePlaneL2ToTempered_apply, MeasureTheory.Lp.toTemperedDistribution_apply]

end WholePlaneHorizontalFibre

end

end FastDynamo

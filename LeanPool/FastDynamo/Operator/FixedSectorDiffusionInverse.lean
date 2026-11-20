/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.FixedSectorResolvent
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Order.Filter.AtTopBot.Defs

/-!
# The positive-real fixed-sector diffusion inverse

In a fixed axial sector `K` the diffusion part of the reduced induction pencil
is the diagonal Fourier multiplier `σ + ε (4π²|n|² + (2πK)²)`.  This module
computes the inverse symbol, proves the scalar estimates it satisfies, and
reconstructs the multiplier as a bounded operator
`reducedInductionDiffusionInverse : TransverseC3L2 →L[ℂ] TransverseC3H2` into
the project's closed Fourier-graph `H²` model.  Everything is restricted to one
axial sector and to *positive real* spectral parameters `σ`, which is exactly
the input of the first step of the large-real resolvent construction.

The two resulting one-sided identities make the multiplier a two-sided
diffusion inverse in the sense of `FastDynamo.Operator.FixedSectorResolvent`.
Hence, whenever the lower-order transport/stretching correction composed with it
has norm `< 1`, one obtains a resolvent of `A_{ε,K}` at `σ`
(`reducedInductionHasResolventOnSingletonOfDiffusionInverse`).

## Contents

* **Fourier symbols for the fixed-sector diffusion pencil.**
  `reducedInductionDiffusionPencilSymbol`,
  `reducedInductionDiffusionInverseSymbol`, their positivity, the bounds
  `symbol⁻¹ ≤ σ⁻¹`, `energy * symbol⁻¹ ≤ ε⁻¹` and
  `energy * (symbol⁻¹)² ≤ (4εσ)⁻¹`, and the decay of the inverse symbol as
  `σ → ∞`.
* **The positive-real fixed-sector diffusion inverse.** Coordinatewise
  transverse Fourier analysis and synthesis, the coefficient multipliers with
  their norm bounds, `reducedInductionDiffusionInverse` with its symbol
  formula, the identities `reducedInductionDiffusionPencil_comp_inverse` and
  `inverse_comp_reducedInductionDiffusionPencil`.
-/

@[expose] public section

/-!
## Fourier symbols for the fixed-sector diffusion pencil

The completely explicit scalar calculation behind the
large-positive-real-parameter part of the fixed-sector argument.  It is purely
algebraic; the estimates are stated in the form required by the
functional-analytic lift of the next section, which carries the scalar
multiplier from the project's `L²` model into its closed Fourier-graph `H²`
model.
-/

namespace FastDynamo

noncomputable section

/-- The nonnegative contribution of the fixed axial Fourier frequency. -/
def fixedSectorAxialEnergy (K : ℤ) : ℝ :=
  (2 * Real.pi * (K : ℝ)) ^ 2

/-- The positive-real diffusion-pencil symbol at transverse frequency `n`. -/
def reducedInductionDiffusionPencilSymbol
    (ε σ : ℝ) (K : ℤ) (n : TransverseFrequency) : ℝ :=
  σ + ε * (transverseFrequencyEnergy n + fixedSectorAxialEnergy K)

/-- The scalar Fourier multiplier of the prospective diffusion inverse. -/
def reducedInductionDiffusionInverseSymbol
    (ε σ : ℝ) (K : ℤ) (n : TransverseFrequency) : ℝ :=
  (reducedInductionDiffusionPencilSymbol ε σ K n)⁻¹

/-- The axial energy `(2πK)²` contributed by the fixed Fourier sector is nonnegative. -/
theorem fixedSectorAxialEnergy_nonneg (K : ℤ) :
    0 ≤ fixedSectorAxialEnergy K := by
  exact sq_nonneg _

/--
For nonnegative diffusivity, the diffusion-pencil symbol at every transverse frequency is at
least the spectral parameter `σ`, since the frequency contribution is nonnegative.
-/
theorem reducedInductionDiffusionPencilSymbol_ge_sigma
    {ε σ : ℝ} (hε : 0 ≤ ε) (K : ℤ) (n : TransverseFrequency) :
    σ ≤ reducedInductionDiffusionPencilSymbol ε σ K n := by
  unfold reducedInductionDiffusionPencilSymbol
  have hsum : 0 ≤ transverseFrequencyEnergy n + fixedSectorAxialEnergy K :=
    add_nonneg (transverseFrequencyEnergy_nonneg n)
      (fixedSectorAxialEnergy_nonneg K)
  nlinarith [mul_nonneg hε hsum]

/--
For nonnegative diffusivity and `σ > 0`, the diffusion-pencil symbol is strictly positive at
every transverse frequency.
-/
theorem reducedInductionDiffusionPencilSymbol_pos
    {ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    0 < reducedInductionDiffusionPencilSymbol ε σ K n :=
  lt_of_lt_of_le hσ (reducedInductionDiffusionPencilSymbol_ge_sigma hε K n)

/--
For nonnegative diffusivity and `σ > 0` the diffusion-pencil symbol never vanishes, so it may be
inverted frequency by frequency.
-/
theorem reducedInductionDiffusionPencilSymbol_ne_zero
    {ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    reducedInductionDiffusionPencilSymbol ε σ K n ≠ 0 :=
  ne_of_gt (reducedInductionDiffusionPencilSymbol_pos hε hσ K n)

/-- Fourier-symbol formula for the diffusion pencil on the positive real ray, at any fibre. -/
theorem transverseCoeff_transverseVecDiffusionPencil_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε σ : ℝ) (K : ℤ) (b : TransverseVecH2 ι)
    (n : TransverseFrequency) (i : ι) :
    transverseCoeffCLM n i
        (transverseVecDiffusionPencil ι ε K (σ : ℂ) b) =
      (reducedInductionDiffusionPencilSymbol ε σ K n : ℂ) *
        transverseCoeffCLM n i (transverseH2Embedding b) := by
  rw [transverseVecDiffusionPencil, sub_apply, smul_apply]
  change transverseCoeffCLM n i
      (↑σ • transverseH2Embedding b - ↑ε •
        (transverseVecLaplacianFromH2 ι b -
          (2 * Real.pi * K : ℂ) ^ 2 • transverseH2Embedding b)) = _
  simp only [map_sub, ContinuousLinearMap.map_smul_of_tower,
    transverseCoeffCLM_transverseLaplacianFromH2]
  have haxial : (2 * Real.pi * K : ℂ) ^ 2 =
      (fixedSectorAxialEnergy K : ℂ) := by
    unfold fixedSectorAxialEnergy
    push_cast
    ring
  rw [haxial]
  unfold reducedInductionDiffusionPencilSymbol
  simp only [Algebra.smul_def]
  simp only [Complex.coe_algebraMap]
  push_cast
  simp
  ring

/-- The inverse scalar multiplier cancels the diffusion symbol. -/
theorem reducedInductionDiffusionPencilSymbol_mul_inverseSymbol
    {ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    reducedInductionDiffusionPencilSymbol ε σ K n *
        reducedInductionDiffusionInverseSymbol ε σ K n = 1 := by
  unfold reducedInductionDiffusionInverseSymbol
  exact mul_inv_cancel₀
    (reducedInductionDiffusionPencilSymbol_ne_zero hε hσ K n)

/-- The order-zero inverse multiplier is bounded by `1 / σ`. -/
theorem reducedInductionDiffusionInverseSymbol_le_inv_sigma
    {ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    reducedInductionDiffusionInverseSymbol ε σ K n ≤ σ⁻¹ := by
  unfold reducedInductionDiffusionInverseSymbol
  exact (inv_le_inv₀
    (reducedInductionDiffusionPencilSymbol_pos hε hσ K n) hσ).2
      (reducedInductionDiffusionPencilSymbol_ge_sigma hε K n)

/-- The order-zero inverse multiplier is nonnegative. -/
theorem reducedInductionDiffusionInverseSymbol_nonneg
    {ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    0 ≤ reducedInductionDiffusionInverseSymbol ε σ K n := by
  unfold reducedInductionDiffusionInverseSymbol
  exact inv_nonneg.mpr
    (le_of_lt (reducedInductionDiffusionPencilSymbol_pos hε hσ K n))

/-- Squared first-order multiplier estimate.  It is the scalar estimate
which yields `O(σ^{-1/2})` after the Fourier-graph reconstruction. -/
theorem transverseFrequencyEnergy_mul_inverseSymbol_sq_le
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    transverseFrequencyEnergy n *
        (reducedInductionDiffusionInverseSymbol ε σ K n) ^ 2 ≤
      (4 * ε * σ)⁻¹ := by
  let e := transverseFrequencyEnergy n + fixedSectorAxialEnergy K
  have he : 0 ≤ e := add_nonneg (transverseFrequencyEnergy_nonneg n)
    (fixedSectorAxialEnergy_nonneg K)
  have hE : transverseFrequencyEnergy n ≤ e := by
    dsimp [e]
    linarith [fixedSectorAxialEnergy_nonneg K]
  have hden : 0 < σ + ε * e := by
    have : σ ≤ σ + ε * e := by nlinarith [mul_nonneg hε.le he]
    exact lt_of_lt_of_le hσ this
  have hsq : 4 * ε * σ * transverseFrequencyEnergy n ≤ (σ + ε * e) ^ 2 := by
    have hmain : 4 * ε * σ * e ≤ (σ + ε * e) ^ 2 := by
      nlinarith [sq_nonneg (σ - ε * e)]
    exact (mul_le_mul_of_nonneg_left hE (by positivity)).trans hmain
  have hpos : 0 < 4 * ε * σ := by positivity
  rw [reducedInductionDiffusionInverseSymbol,
    reducedInductionDiffusionPencilSymbol]
  change transverseFrequencyEnergy n * (σ + ε *
      (transverseFrequencyEnergy n + fixedSectorAxialEnergy K))⁻¹ ^ 2 ≤ _
  rw [inv_pow, ← div_eq_mul_inv, inv_eq_one_div]
  apply (div_le_iff₀ (sq_pos_of_pos hden)).2
  have hdiv : transverseFrequencyEnergy n ≤
      (σ + ε * e) ^ 2 / (4 * ε * σ) :=
    (le_div_iff₀ hpos).2 (by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hsq)
  simpa [e, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

end

end FastDynamo

/-!
## The positive-real fixed-sector diffusion inverse

The diagonal Fourier multiplier of the previous section is reconstructed as a
bounded map from transverse `L²` into the project's closed Fourier-graph `H²`
domain.  It is restricted to one fixed axial sector and positive
real spectral parameters.
-/

namespace FastDynamo

noncomputable section

/-- Coordinatewise transverse Fourier analysis on the fibre `ℂ^ι`. -/
def transverseVecFourierAnalysis (ι : Type*) [Fintype ι] :
    TransverseVecL2 ι →L[ℂ] WeightedTransverseCoeffs ι :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : ι => TransverseScalarFourierL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      transverseScalarFourierAnalysis.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (transverseCoordL2 i))

/-- Coordinatewise transverse Fourier analysis. -/
abbrev transverseC3FourierAnalysis :
    TransverseC3L2 →L[ℂ] WeightedTransverseC3Coeffs :=
  transverseVecFourierAnalysis (Fin 3)

/--
Coordinatewise Fourier analysis acts in each component by scalar Fourier analysis of the
corresponding coordinate field.
-/
@[simp] theorem transverseVecFourierAnalysis_apply {ι : Type*} [Fintype ι]
    (f : TransverseVecL2 ι) (i : ι) :
    transverseVecFourierAnalysis ι f i =
      transverseScalarFourierAnalysis (transverseCoordL2 i f) :=
  rfl

-- This is the definitional coordinate projection of the bundled analysis;
-- keeping it as a simp rule avoids repeatedly unfolding the PiLp equivalence.
/--
The `n`-th entry of the `i`-th component of the analysis of `f` is the Fourier coefficient
`transverseCoeffCLM n i f`.
-/
theorem transverseVecFourierAnalysisCoeff {ι : Type*} [Fintype ι]
    (f : TransverseVecL2 ι) (n : TransverseFrequency) (i : ι) :
    (transverseVecFourierAnalysis ι f i) n = transverseCoeffCLM n i f :=
  rfl

/-- Three-component form of the coefficient identity for Fourier analysis. -/
theorem transverseC3FourierAnalysisCoeff
    (f : TransverseC3L2) (n : TransverseFrequency) (i : Fin 3) :
    (transverseC3FourierAnalysis f i) n = transverseCoeffCLM n i f :=
  rfl

/-- Apply one scalar Fourier-coefficient operator to each fibre component. -/
def mapWeightedVecFourierCoords (ι : Type*)
    (T : TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2) :
    WeightedTransverseCoeffs ι →L[ℂ] WeightedTransverseCoeffs ι :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : ι => TransverseScalarFourierL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => T.comp
      (PiLp.proj 2 (fun _ : ι => TransverseScalarFourierL2) i))

/--
`mapWeightedVecFourierCoords ι T` applies the scalar coefficient operator `T` separately in
each fibre component.
-/
@[simp] theorem mapWeightedVecFourierCoords_apply {ι : Type*}
    (T : TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2)
    (a : WeightedTransverseCoeffs ι) (i : ι) :
    mapWeightedVecFourierCoords ι T a i = T (a i) :=
  rfl

/-- Coordinatewise transverse Fourier synthesis on the fibre `ℂ^ι`. -/
def transverseVecFourierSynthesis (ι : Type*) [Fintype ι] [DecidableEq ι] :
    WeightedTransverseCoeffs ι →L[ℂ] TransverseVecL2 ι :=
  transverseVecOfCoordsL2.comp
    (mapWeightedTransverseCoords transverseScalarFourierSynthesis)

/-- Coordinatewise transverse Fourier synthesis. -/
abbrev transverseC3FourierSynthesis :
    WeightedTransverseC3Coeffs →L[ℂ] TransverseC3L2 :=
  transverseVecFourierSynthesis (Fin 3)

/--
The Fourier coefficients of a coordinatewise synthesis are exactly the coefficient array it was
built from.
-/
theorem transverseCoeffCLM_transverseVecFourierSynthesis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : WeightedTransverseCoeffs ι) (n : TransverseFrequency) (i : ι) :
    transverseCoeffCLM n i (transverseVecFourierSynthesis ι a) = (a i) n :=
  transverseCoeffCLM_transverseVecOfCoordsL2_synthesis a n i

/-- The scalar positive-real diffusion inverse multiplier. -/
def reducedInductionDiffusionInverseCoeffMultiplier
    (ε σ : ℝ) (K : ℤ) (n : TransverseFrequency) : ℂ :=
  (reducedInductionDiffusionInverseSymbol ε σ K n : ℂ)

/-- The corresponding multiplier for the stored weighted `H²` coefficients. -/
def reducedInductionDiffusionInverseWeightedCoeffMultiplier
    (ε σ : ℝ) (K : ℤ) (n : TransverseFrequency) : ℂ :=
  (transverseH2Weight n : ℂ) *
    reducedInductionDiffusionInverseCoeffMultiplier ε σ K n

/--
For `0 ≤ ε` and `0 < σ` the order-zero diffusion-inverse multiplier has modulus at most `σ⁻¹`,
uniformly in the transverse frequency.
-/
theorem norm_reducedInductionDiffusionInverseCoeffMultiplier_le
    {ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    ‖reducedInductionDiffusionInverseCoeffMultiplier ε σ K n‖ ≤ σ⁻¹ := by
  rw [reducedInductionDiffusionInverseCoeffMultiplier, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (reducedInductionDiffusionInverseSymbol_nonneg hε hσ K n)]
  exact reducedInductionDiffusionInverseSymbol_le_inv_sigma hε hσ K n

/--
For positive `ε` and `σ`, the order-two weight is dominated by `(σ⁻¹ + ε⁻¹)` times the
diffusion-pencil symbol; this is the elliptic gain that makes the inverse land in `H²`.
-/
private theorem transverseH2Weight_le_diffusion_bound_times_symbol
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    transverseH2Weight n ≤ (σ⁻¹ + ε⁻¹) *
      reducedInductionDiffusionPencilSymbol ε σ K n := by
  unfold transverseH2Weight reducedInductionDiffusionPencilSymbol
  have hE : 0 ≤ transverseFrequencyEnergy n := transverseFrequencyEnergy_nonneg n
  have hA : 0 ≤ fixedSectorAxialEnergy K := fixedSectorAxialEnergy_nonneg K
  have hσi : 0 < σ⁻¹ := inv_pos.mpr hσ
  have hεi : 0 < ε⁻¹ := inv_pos.mpr hε
  field_simp [hσ.ne', hε.ne']
  nlinarith [mul_nonneg hε.le hE, mul_nonneg hε.le hA]

/--
For positive `ε` and `σ` the weighted diffusion-inverse multiplier, which carries the extra
factor `transverseH2Weight n`, is bounded uniformly by `σ⁻¹ + ε⁻¹`.
-/
theorem norm_reducedInductionDiffusionInverseWeightedCoeffMultiplier_le
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    ‖reducedInductionDiffusionInverseWeightedCoeffMultiplier ε σ K n‖ ≤
      σ⁻¹ + ε⁻¹ := by
  simp only [reducedInductionDiffusionInverseWeightedCoeffMultiplier,
    reducedInductionDiffusionInverseCoeffMultiplier, norm_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (transverseH2Weight_pos n),
    abs_of_nonneg (reducedInductionDiffusionInverseSymbol_nonneg hε.le hσ K n)]
  let d := reducedInductionDiffusionPencilSymbol ε σ K n
  have hd : 0 < d := reducedInductionDiffusionPencilSymbol_pos hε.le hσ K n
  have hbound := transverseH2Weight_le_diffusion_bound_times_symbol hε hσ K n
  change transverseH2Weight n * d⁻¹ ≤ σ⁻¹ + ε⁻¹
  rw [← div_eq_mul_inv]
  exact (div_le_iff₀ hd).2 (by simpa [d, mul_comm, mul_left_comm, mul_assoc] using hbound)

/-- The bounded scalar coefficient map for the physical component of the
diffusion inverse. -/
def reducedInductionDiffusionInverseCoeffMap
    (ε σ : ℝ) (K : ℤ) (hε : 0 ≤ ε) (hσ : 0 < σ) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ)
      (reducedInductionDiffusionInverseCoeffMultiplier ε σ K n))
    (inv_nonneg.mpr hσ.le)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (reducedInductionDiffusionInverseCoeffMultiplier ε σ K n)).trans
        (norm_reducedInductionDiffusionInverseCoeffMultiplier_le hε hσ K n))

/--
The order-zero diffusion-inverse coefficient map acts diagonally, multiplying the `n`-th
coefficient by `reducedInductionDiffusionInverseCoeffMultiplier ε σ K n`.
-/
@[simp] theorem reducedInductionDiffusionInverseCoeffMap_apply
    (ε σ : ℝ) (K : ℤ) (hε : 0 ≤ ε) (hσ : 0 < σ)
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    reducedInductionDiffusionInverseCoeffMap ε σ K hε hσ a n =
    reducedInductionDiffusionInverseCoeffMultiplier ε σ K n * a n :=
  rfl

/-- Operator-norm version of the order-zero Fourier multiplier bound. -/
theorem norm_reducedInductionDiffusionInverseCoeffMap_le
    (ε σ : ℝ) (K : ℤ) (hε : 0 ≤ ε) (hσ : 0 < σ) :
    ‖reducedInductionDiffusionInverseCoeffMap ε σ K hε hσ‖ ≤ σ⁻¹ := by
  exact lp.norm_mapCLM_le 2 _ (inv_nonneg.mpr hσ.le)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (reducedInductionDiffusionInverseCoeffMultiplier ε σ K n)).trans
        (norm_reducedInductionDiffusionInverseCoeffMultiplier_le hε hσ K n))

/-- The bounded scalar coefficient map for the weighted `H²` component of
the diffusion inverse. -/
def reducedInductionDiffusionInverseWeightedCoeffMap
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ)
      (reducedInductionDiffusionInverseWeightedCoeffMultiplier ε σ K n))
    (by positivity)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (reducedInductionDiffusionInverseWeightedCoeffMultiplier ε σ K n)).trans
        (norm_reducedInductionDiffusionInverseWeightedCoeffMultiplier_le hε hσ K n))

/--
The weighted diffusion-inverse coefficient map acts diagonally, multiplying the `n`-th
coefficient by the weighted multiplier.
-/
@[simp] theorem reducedInductionDiffusionInverseWeightedCoeffMap_apply
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    reducedInductionDiffusionInverseWeightedCoeffMap ε σ K hε hσ a n =
    reducedInductionDiffusionInverseWeightedCoeffMultiplier ε σ K n * a n :=
  rfl

section FibreGeneric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The physical `L²` component of the diagonal diffusion inverse on the fibre `ℂ^ι`. -/
def transverseVecDiffusionInversePhysical (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    TransverseVecL2 ι →L[ℂ] TransverseVecL2 ι :=
  (transverseVecFourierSynthesis ι).comp
    ((mapWeightedVecFourierCoords ι
      (reducedInductionDiffusionInverseCoeffMap ε σ K hε.le hσ)).comp
        (transverseVecFourierAnalysis ι))

/-- The stored weighted-coefficient component of the diagonal diffusion inverse on `ℂ^ι`. -/
def transverseVecDiffusionInverseWeighted (ι : Type*) [Fintype ι]
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    TransverseVecL2 ι →L[ℂ] WeightedTransverseCoeffs ι :=
  (mapWeightedVecFourierCoords ι
    (reducedInductionDiffusionInverseWeightedCoeffMap ε σ K hε hσ)).comp
      (transverseVecFourierAnalysis ι)

/--
The physical and weighted components produced by the diagonal multiplier satisfy the transverse
`H²` graph equation, so the pair lies in `transverseH2Submodule`.
-/
theorem transverseVecDiffusionInverse_graph_mem
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (f : TransverseVecL2 ι) :
    (transverseVecDiffusionInversePhysical ι ε σ K hε hσ f,
      transverseVecDiffusionInverseWeighted ι ε σ K hε hσ f) ∈
        transverseH2Submodule := by
  rw [mem_transverseH2Submodule_iff]
  intro n i
  simp only [transverseVecDiffusionInversePhysical,
    transverseVecDiffusionInverseWeighted,
    ContinuousLinearMap.comp_apply,
    transverseCoeffCLM_transverseVecFourierSynthesis,
    mapWeightedVecFourierCoords_apply,
    reducedInductionDiffusionInverseCoeffMap_apply,
    reducedInductionDiffusionInverseWeightedCoeffMap_apply,
    transverseVecFourierAnalysisCoeff,
    reducedInductionDiffusionInverseWeightedCoeffMultiplier,
    reducedInductionDiffusionInverseCoeffMultiplier]
  ring

/-- The bounded positive-real diffusion inverse from transverse `L²` into the
closed Fourier-graph transverse `H²` space of the fibre `ℂ^ι`. -/
def transverseVecDiffusionInverse (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    TransverseVecL2 ι →L[ℂ] TransverseVecH2 ι :=
  ((transverseVecDiffusionInversePhysical ι ε σ K hε hσ).prod
    (transverseVecDiffusionInverseWeighted ι ε σ K hε hσ)).codRestrict
      transverseH2Submodule
      (transverseVecDiffusionInverse_graph_mem ε σ K hε hσ)

/-- The bounded positive-real diffusion inverse from transverse `L²` into the
closed Fourier-graph transverse `H²` space. -/
abbrev reducedInductionDiffusionInverse
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    TransverseC3L2 →L[ℂ] TransverseC3H2 :=
  transverseVecDiffusionInverse (Fin 3) ε σ K hε hσ

-- The codomain restriction stores this physical component definitionally.
/--
The physical `L²` field underlying the diffusion inverse is
`transverseVecDiffusionInversePhysical`, stored definitionally by the codomain restriction.
-/
theorem transverseH2EmbeddingTransverseVecDiffusionInverse
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (f : TransverseVecL2 ι) :
    transverseH2Embedding
      (transverseVecDiffusionInverse ι ε σ K hε hσ f) =
      transverseVecDiffusionInversePhysical ι ε σ K hε hσ f :=
  rfl

/--
Fourier-symbol formula for the diffusion inverse: it multiplies each coefficient of `f` by
`reducedInductionDiffusionInverseCoeffMultiplier ε σ K n`.
-/
theorem transverseCoeff_transverseVecDiffusionInverse
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (f : TransverseVecL2 ι) (n : TransverseFrequency) (i : ι) :
    transverseCoeffCLM n i
      (transverseH2Embedding
        (transverseVecDiffusionInverse ι ε σ K hε hσ f)) =
      reducedInductionDiffusionInverseCoeffMultiplier ε σ K n *
        transverseCoeffCLM n i f := by
  simp only [transverseH2EmbeddingTransverseVecDiffusionInverse,
    transverseVecDiffusionInversePhysical, ContinuousLinearMap.comp_apply,
    transverseCoeffCLM_transverseVecFourierSynthesis,
    mapWeightedVecFourierCoords_apply,
    reducedInductionDiffusionInverseCoeffMap_apply,
    transverseVecFourierAnalysisCoeff]

/-- Three-component form of the Fourier-symbol formula for the diffusion inverse. -/
theorem transverseCoeff_reducedInductionDiffusionInverse
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (f : TransverseC3L2) (n : TransverseFrequency) (i : Fin 3) :
    transverseCoeffCLM n i
      (transverseH2Embedding
        (reducedInductionDiffusionInverse ε σ K hε hσ f)) =
      reducedInductionDiffusionInverseCoeffMultiplier ε σ K n *
        transverseCoeffCLM n i f :=
  transverseCoeff_transverseVecDiffusionInverse ε σ K hε hσ f n i

/--
The complexified diffusion-pencil symbol and the inverse multiplier are reciprocal at every
transverse frequency.
-/
private theorem reducedInductionDiffusionPencilSymbol_mul_inverseCoeffMultiplier
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    (reducedInductionDiffusionPencilSymbol ε σ K n : ℂ) *
      reducedInductionDiffusionInverseCoeffMultiplier ε σ K n = 1 := by
  simp only [reducedInductionDiffusionInverseCoeffMultiplier]
  norm_cast
  exact reducedInductionDiffusionPencilSymbol_mul_inverseSymbol hε.le hσ K n

/-- The reconstructed multiplier is a right inverse of the fixed-sector
diffusion pencil at every positive real parameter and every fibre. -/
theorem transverseVecDiffusionPencil_comp_inverse
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    (transverseVecDiffusionPencil ι ε K (σ : ℂ)).comp
      (transverseVecDiffusionInverse ι ε σ K hε hσ) =
        ContinuousLinearMap.id ℂ (TransverseVecL2 ι) := by
  apply ContinuousLinearMap.ext
  intro f
  apply transverseVecL2_ext_coeff
  intro n i
  rw [ContinuousLinearMap.comp_apply,
    transverseCoeff_transverseVecDiffusionPencil_real,
    transverseCoeff_transverseVecDiffusionInverse, ← mul_assoc,
    reducedInductionDiffusionPencilSymbol_mul_inverseCoeffMultiplier hε hσ]
  simp only [one_mul, ContinuousLinearMap.id_apply]

/-- The reconstructed multiplier is also a left inverse of the fixed-sector
diffusion pencil at every positive real parameter and every fibre. -/
theorem inverse_comp_transverseVecDiffusionPencil
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    (transverseVecDiffusionInverse ι ε σ K hε hσ).comp
      (transverseVecDiffusionPencil ι ε K (σ : ℂ)) =
        ContinuousLinearMap.id ℂ (TransverseVecH2 ι) := by
  apply ContinuousLinearMap.ext
  intro b
  apply transverseH2Embedding_injective
  apply transverseVecL2_ext_coeff
  intro n i
  rw [ContinuousLinearMap.comp_apply,
    transverseCoeff_transverseVecDiffusionInverse,
    transverseCoeff_transverseVecDiffusionPencil_real]
  have hmul :=
    reducedInductionDiffusionPencilSymbol_mul_inverseCoeffMultiplier hε hσ K n
  simp only [ContinuousLinearMap.id_apply]
  rw [← mul_assoc, mul_comm
    (reducedInductionDiffusionInverseCoeffMultiplier ε σ K n), hmul, one_mul]

end FibreGeneric

/-- The reconstructed multiplier is a right inverse of the fixed-sector
diffusion pencil at every positive real parameter. -/
theorem reducedInductionDiffusionPencil_comp_inverse
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    (reducedInductionDiffusionPencil ε K (σ : ℂ)).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ) =
        ContinuousLinearMap.id ℂ TransverseC3L2 :=
  transverseVecDiffusionPencil_comp_inverse ε σ K hε hσ

/-- The reconstructed multiplier is also a left inverse of the fixed-sector
diffusion pencil at every positive real parameter. -/
theorem inverse_comp_reducedInductionDiffusionPencil
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    (reducedInductionDiffusionInverse ε σ K hε hσ).comp
      (reducedInductionDiffusionPencil ε K (σ : ℂ)) =
        ContinuousLinearMap.id ℂ TransverseC3H2 :=
  inverse_comp_transverseVecDiffusionPencil ε σ K hε hσ

end

end FastDynamo

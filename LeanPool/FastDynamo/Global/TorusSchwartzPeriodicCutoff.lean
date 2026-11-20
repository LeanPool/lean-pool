/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.TransverseSmoothBumpPeriodization

/-!
# Periodic second-order cut-off multipliers built from an arbitrary plane bump

The paper (§7.1, `sec:parametrix`) uses three placed scalar cut-offs `φ_n`, `ψ_n`, `χ_n`
around the selected cell, and needs each of them as a bounded multiplier of the periodic
`H²` Fourier graph, together with sup
bounds on their derivatives.  The paper's `eq:parametrix-cutoff-bounds` is the
two-term display `‖D^jψ_n‖_∞ + ‖D^jχ_n‖_∞ ≤ CR_n^{-j}`: the input cut-off `φ_n` only splits the
right-hand side and never enters a commutator, so only the two output cut-offs need derivative
bounds, and no summand `‖D^jφ_n‖_∞` appears.  The
explicit construction here bounds all three anyway, and the `φ_n` bound is simply never read.

`FastDynamo/Analysis/TransverseSmoothBumpH2CutoffConcrete.lean` performs that construction for
the two bumps `inputCutoff` and `outputCutoff`; this module isolates
the same construction for an **arbitrary** compactly supported smooth plane bump, presented as a
Schwartz function, and adds the two further ingredients the parametrix needs:

* the identification of the *stored Laplacian* of the completed cut-off with the lattice
  periodization of the whole-plane Laplacian of the bump (the value and the stored gradient are
  identified in the construction above), and
* the resulting sup-norm bounds `‖value‖_∞`, `‖gradient j‖_∞`, `‖laplacian‖_∞` in terms of
  pointwise bounds for the bump and for its first and second derivatives on the plane.

Nothing here is specific to a cell: the caller supplies the bump, the no-wrap support hypothesis
(`SupportedInIocFundamentalBox`, the statement that the support does not wrap around the
transverse torus) and the pointwise bounds.  `FastDynamo/Global/TorusPlacedCutoffC2.lean`
instantiates it at the three placed profiles of a cell.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform LineDeriv SchwartzMap

namespace SchwartzPeriodicCutoff

open PeriodicSecondOrderCutoffs
open TransverseH2CutoffMultiplier
open TransverseSmoothBumpH2Cutoff
open TransverseSmoothBumpH2CutoffConcrete
open TransverseSmoothBumpPeriodization
open TransverseSmoothH2CutoffMultiplier

/-! ## Lattice Fourier samples of an arbitrary Schwartz bump -/

/-- The integer-lattice samples of the whole-plane Fourier transform of a Schwartz bump. -/
def fourierSample (F : SchwartzMap WholePlane ℂ) : TransverseFrequency → ℂ :=
  fun n ↦ 𝓕 F (frequencyPoint n)

/-- Schwartz decay gives arbitrary polynomial decay of the lattice Fourier samples. -/
theorem fourierSample_hasRapidDecay (F : SchwartzMap WholePlane ℂ) :
    HasRapidDecayOnFrequencyLattice (fourierSample F) := by
  intro k
  rcases (𝓕 F).decay k 0 with ⟨C, _hC, hbound⟩
  refine ⟨C, fun n ↦ ?_⟩
  simpa [fourierSample] using hbound (frequencyPoint n)

/-- The lattice Fourier samples of a Schwartz bump satisfy the simultaneous second-order
summability premise of the periodic cut-off completion. -/
theorem hasSummableSecondOrderFourierWeight_fourierSample
    (F : SchwartzMap WholePlane ℂ) :
    HasSummableSecondOrderFourierWeight (fourierSample F) := by
  apply hasSummableSecondOrderFourierWeight_of_scalar
  exact summable_norm_mul_of_rapidDecay_polynomialGrowth
    (fourierSample_hasRapidDecay F) secondOrderFourierWeight_nonneg
    secondOrderFourierWeight_hasPolynomialGrowth

/-- The periodic second-order cut-off multiplier attached to an arbitrary Schwartz bump. -/
def cutoff (F : SchwartzMap WholePlane ℂ) : PeriodicSecondOrderCutoff :=
  summableFourierPeriodicSecondOrderCutoff (fourierSample F)
    (hasSummableSecondOrderFourierWeight_fourierSample F)

/-- The Fourier coefficients of the completed value are the lattice Fourier samples. -/
theorem cutoff_value_coeff (F : SchwartzMap WholePlane ℂ) (q : TransverseFrequency) :
    transverseScalarCoeffCLM q (transverseScalarLInfToL2 (cutoff F).value) =
      fourierSample F q :=
  transverseScalarCoeff_completedSecondOrderValue (fourierSample F)
    (hasSummableSecondOrderFourierWeight_fourierSample F) q

/-! ## The stored gradient and Laplacian of a completed cut-off -/

/-- Coefficient extraction from one gradient component of a simultaneous second-order
package, as one continuous functional. -/
def packageGradientCoeff (j : Fin 2) (q : TransverseFrequency) :
    SecondOrderCutoffPackage →L[ℂ] ℂ :=
  (transverseScalarCoeffCLM q).comp
    (transverseScalarLInfToL2.comp (packageGradientCoord j))

/-- On a single-frequency package the gradient coefficient functional acts by the derivative
symbol `2πin_j` at its own frequency and vanishes elsewhere. -/
theorem packageGradientCoeff_coefficient
    (j : Fin 2) (q n : TransverseFrequency) (c : ℂ) :
    packageGradientCoeff j q (coefficientSecondOrderPackage n c) =
      if q = n then transverseFourierDerivMultiplier j n * c else 0 := by
  change transverseScalarCoeffCLM q
    (transverseScalarLInfToL2
      (packageGradientCoord j (coefficientSecondOrderPackage n c))) = _
  simp only [packageGradientCoord_apply, coefficientSecondOrderPackage]
  rw [polynomialDeriv_single, polynomialLInf_single, map_smul, map_smul,
    transverseScalarCoeff_monomialLInf]
  split_ifs <;> simp_all

/-- The completed gradient field has the differentiated coefficient family from which the
simultaneous package was built. -/
theorem completedSecondOrderGradient_coeff
    (a : TransverseFrequency → ℂ)
    (ha : HasSummableSecondOrderFourierWeight a) (j : Fin 2) (q : TransverseFrequency) :
    transverseScalarCoeffCLM q
        (transverseScalarLInfToL2
          (packageGradientCoord j (completedSecondOrderPackage a))) =
      transverseFourierDerivMultiplier j q * a q := by
  change packageGradientCoeff j q (completedSecondOrderPackage a) = _
  unfold completedSecondOrderPackage
  rw [(packageGradientCoeff j q).map_tsum (summable_secondOrderPackageSeries ha)]
  rw [tsum_eq_single q]
  · rw [secondOrderPackageSeries, packageGradientCoeff_coefficient, ite_eq_left rfl]
  · intro n hn
    rw [secondOrderPackageSeries, packageGradientCoeff_coefficient]
    exact ite_eq_right (Ne.symm hn)

/-- The Fourier coefficients of the stored gradient carry the derivative symbol `2πin_j`. -/
theorem cutoff_gradient_coeff (F : SchwartzMap WholePlane ℂ) (j : Fin 2)
    (q : TransverseFrequency) :
    transverseScalarCoeffCLM q (transverseScalarLInfToL2 ((cutoff F).gradient j)) =
      transverseFourierDerivMultiplier j q * fourierSample F q :=
  completedSecondOrderGradient_coeff (fourierSample F)
    (hasSummableSecondOrderFourierWeight_fourierSample F) j q

/-- Coefficient extraction from the Laplacian component of a simultaneous second-order
package, as one continuous functional. -/
def packageLaplacianCoeff (q : TransverseFrequency) :
    SecondOrderCutoffPackage →L[ℂ] ℂ :=
  (transverseScalarCoeffCLM q).comp
    (transverseScalarLInfToL2.comp packageLaplacian)

/-- On a single-frequency package the Laplacian coefficient functional acts by the symbol
`-4π²|n|²` at its own frequency and vanishes elsewhere. -/
theorem packageLaplacianCoeff_coefficient
    (q n : TransverseFrequency) (c : ℂ) :
    packageLaplacianCoeff q (coefficientSecondOrderPackage n c) =
      if q = n then -(transverseFrequencyEnergy n : ℂ) * c else 0 := by
  change transverseScalarCoeffCLM q
    (transverseScalarLInfToL2 (packageLaplacian (coefficientSecondOrderPackage n c))) = _
  simp only [packageLaplacian_apply, coefficientSecondOrderPackage]
  rw [polynomialLaplacian_single, polynomialLInf_single, map_smul, map_smul,
    transverseScalarCoeff_monomialLInf]
  split_ifs <;> simp_all

/-- The completed Laplacian field has the twice-differentiated coefficient family from which
the simultaneous package was built. -/
theorem transverseScalarCoeff_completedSecondOrderLaplacian
    (a : TransverseFrequency → ℂ)
    (ha : HasSummableSecondOrderFourierWeight a) (q : TransverseFrequency) :
    transverseScalarCoeffCLM q
        (transverseScalarLInfToL2 (packageLaplacian (completedSecondOrderPackage a))) =
      -(transverseFrequencyEnergy q : ℂ) * a q := by
  change packageLaplacianCoeff q (completedSecondOrderPackage a) = _
  unfold completedSecondOrderPackage
  rw [(packageLaplacianCoeff q).map_tsum (summable_secondOrderPackageSeries ha)]
  rw [tsum_eq_single q]
  · rw [secondOrderPackageSeries, packageLaplacianCoeff_coefficient, ite_eq_left rfl]
  · intro n hn
    rw [secondOrderPackageSeries, packageLaplacianCoeff_coefficient]
    exact ite_eq_right (Ne.symm hn)

/-- The Fourier coefficients of the stored Laplacian carry the symbol `-4π²|n|²`. -/
theorem cutoff_laplacian_coeff (F : SchwartzMap WholePlane ℂ) (q : TransverseFrequency) :
    transverseScalarCoeffCLM q (transverseScalarLInfToL2 (cutoff F).laplacian) =
      -(transverseFrequencyEnergy q : ℂ) * fourierSample F q :=
  transverseScalarCoeff_completedSecondOrderLaplacian (fourierSample F)
    (hasSummableSecondOrderFourierWeight_fourierSample F) q

/-! ## Whole-plane derivatives of the bump -/

/-- The Fourier samples of one whole-plane coordinate derivative carry the same symbol
`2πin_j` as the stored periodic gradient. -/
theorem fourierSample_lineDerivOp (F : SchwartzMap WholePlane ℂ) (j : Fin 2)
    (q : TransverseFrequency) :
    fourierSample (∂_{wholePlaneBasis j} F) q =
      transverseFourierDerivMultiplier j q * fourierSample F q := by
  have hgrowth :
      (fun x : WholePlane ↦ inner ℝ x (wholePlaneBasis j)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (wholePlaneBasis j)).hasTemperateGrowth
  change 𝓕 (∂_{wholePlaneBasis j} F) (frequencyPoint q) = _
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth]
  simp [transverseFourierDerivMultiplier, fourierSample, inner_wholePlaneBasis, smul_eq_mul,
    mul_assoc]

/-- The transverse Laplacian of a Schwartz bump, as a Schwartz function. -/
def schwartzLaplacian (F : SchwartzMap WholePlane ℂ) : SchwartzMap WholePlane ℂ :=
  ∑ j : Fin 2, ∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F)

/-- The transverse Laplacian of a Schwartz bump evaluates as the sum of the two repeated
coordinate derivatives. -/
theorem schwartzLaplacian_apply (F : SchwartzMap WholePlane ℂ) (x : WholePlane) :
    schwartzLaplacian F x =
      ∑ j : Fin 2, (∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F)) x := by
  rw [schwartzLaplacian, sum_apply]

/-- The Fourier samples of the Laplacian carry the symbol `-4π²|n|²`, matching the stored
Laplacian of the completed periodic cut-off. -/
theorem fourierSample_schwartzLaplacian (F : SchwartzMap WholePlane ℂ)
    (q : TransverseFrequency) :
    fourierSample (schwartzLaplacian F) q =
      -(transverseFrequencyEnergy q : ℂ) * fourierSample F q := by
  have hsum : fourierSample (schwartzLaplacian F) q =
      ∑ j : Fin 2, fourierSample (∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F)) q := by
    have hmap : (𝓕 (∑ j : Fin 2,
        ∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F)) : SchwartzMap WholePlane ℂ) =
        ∑ j : Fin 2, 𝓕 (∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F)) := by
      simp
    change 𝓕 (schwartzLaplacian F) (frequencyPoint q) = _
    rw [schwartzLaplacian, hmap, sum_apply]
    rfl
  rw [hsum]
  have hterm : ∀ j : Fin 2,
      fourierSample (∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F)) q =
        (transverseFourierDerivMultiplier j q) ^ 2 * fourierSample F q := by
    intro j
    rw [fourierSample_lineDerivOp, fourierSample_lineDerivOp]
    ring
  simp only [hterm, ← Finset.sum_mul]
  congr 1
  have hsq : ∀ j : Fin 2, (transverseFourierDerivMultiplier j q) ^ 2 =
      -((2 * Real.pi) ^ 2 * ((q j : ℝ) : ℂ) ^ 2) := by
    intro j
    rw [transverseFourierDerivMultiplier]
    have : (Complex.I) ^ 2 = -1 := Complex.I_sq
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [hsq, transverseFrequencyEnergy]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

/-! ## Support of the plane derivatives -/

/-- A Schwartz bump whose closed support lies in a set contained in the half-open unit box
wraps onto the torus without overlap. -/
theorem supportedInIocFundamentalBox_of_tsupport_subset
    (F : SchwartzMap WholePlane ℂ) {S : Set WholePlane}
    (hF : tsupport (F : WholePlane → ℂ) ⊆ S)
    (hS : S ⊆ wholePlaneIocFundamentalBox) :
    SupportedInIocFundamentalBox (F : WholePlane → ℂ) :=
  fun _ hx ↦ hS (hF (subset_closure hx))

/-- Each coordinate derivative of a Schwartz bump has closed support inside that of the
bump itself. -/
theorem tsupport_lineDerivOp_subset (F : SchwartzMap WholePlane ℂ) (j : Fin 2) :
    tsupport ((∂_{wholePlaneBasis j} F : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) ⊆
      tsupport (F : WholePlane → ℂ) :=
  SchwartzMap.tsupport_lineDerivOp_subset (wholePlaneBasis j) F

/-- The transverse Laplacian of a Schwartz bump is supported inside the closed support of
the bump itself. -/
theorem support_schwartzLaplacian_subset (F : SchwartzMap WholePlane ℂ) :
    Function.support ((schwartzLaplacian F : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) ⊆
      tsupport (F : WholePlane → ℂ) := by
  intro x hx
  by_contra hxn
  have hterm : ∀ j : Fin 2, (∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F)) x = 0 := by
    intro j
    have h1 :
        tsupport ((∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F) :
            SchwartzMap WholePlane ℂ) : WholePlane → ℂ) ⊆
          tsupport (F : WholePlane → ℂ) :=
      (tsupport_lineDerivOp_subset _ j).trans (tsupport_lineDerivOp_subset F j)
    have hnot : x ∉ Function.support
        ((∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F) :
          SchwartzMap WholePlane ℂ) : WholePlane → ℂ) :=
      fun hmem ↦ hxn (h1 (subset_closure hmem))
    simpa [Function.mem_support] using hnot
  exact hx (by rw [schwartzLaplacian_apply]; exact Finset.sum_eq_zero fun j _ ↦ hterm j)

/-! ## Identification with the lattice periodization -/

/-- Under the no-wrap hypothesis the completed value is the quotient periodization in `L²`. -/
theorem cutoff_value_eq_periodizationL2 (F : SchwartzMap WholePlane ℂ)
    (hF : SupportedInIocFundamentalBox (F : WholePlane → ℂ)) :
    transverseScalarLInfToL2 (cutoff F).value = torusLatticePeriodizationL2 F hF := by
  apply transverseScalarL2_ext_coeff
  intro q
  rw [cutoff_value_coeff, transverseScalarCoeff_torusLatticePeriodizationL2]
  rfl

/-- Under the no-wrap hypothesis the completed value is represented by the bump evaluated at
the canonical `(0,1]²` representative. -/
theorem cutoff_value_ae_representative (F : SchwartzMap WholePlane ℂ)
    (hF : SupportedInIocFundamentalBox (F : WholePlane → ℂ)) :
    ((cutoff F).value : TransverseTorus → ℂ) =ᵐ[transverseMeasure]
      fun q ↦ F (wholePlaneIocRepresentative q) := by
  have hinclude := transverseScalarLInfToL2_coe_ae (cutoff F).value
  have hperiod := torusLatticePeriodizationL2_coe_ae F hF
  rw [cutoff_value_eq_periodizationL2 F hF] at hinclude
  filter_upwards [hinclude.symm.trans hperiod] with q hq
  rw [hq, torusLatticePeriodization_eq_representative F hF q]

/-- Under the no-wrap hypothesis for the coordinate derivative, the stored gradient component
is the quotient periodization of the whole-plane derivative in `L²`. -/
theorem cutoff_gradient_eq_periodizationL2 (F : SchwartzMap WholePlane ℂ) (j : Fin 2)
    (hG : SupportedInIocFundamentalBox
      ((∂_{wholePlaneBasis j} F : SchwartzMap WholePlane ℂ) : WholePlane → ℂ)) :
    transverseScalarLInfToL2 ((cutoff F).gradient j) =
      torusLatticePeriodizationL2 (∂_{wholePlaneBasis j} F) hG := by
  apply transverseScalarL2_ext_coeff
  intro q
  rw [cutoff_gradient_coeff, transverseScalarCoeff_torusLatticePeriodizationL2]
  exact (fourierSample_lineDerivOp F j q).symm

/-- Almost-everywhere representative form of the stored gradient identification. -/
theorem cutoff_gradient_ae_representative (F : SchwartzMap WholePlane ℂ) (j : Fin 2)
    (hG : SupportedInIocFundamentalBox
      ((∂_{wholePlaneBasis j} F : SchwartzMap WholePlane ℂ) : WholePlane → ℂ)) :
    (((cutoff F).gradient j) : TransverseTorus → ℂ) =ᵐ[transverseMeasure]
      fun q ↦ (∂_{wholePlaneBasis j} F) (wholePlaneIocRepresentative q) := by
  have hinclude := transverseScalarLInfToL2_coe_ae ((cutoff F).gradient j)
  have hperiod := torusLatticePeriodizationL2_coe_ae (∂_{wholePlaneBasis j} F) hG
  rw [cutoff_gradient_eq_periodizationL2 F j hG] at hinclude
  filter_upwards [hinclude.symm.trans hperiod] with q hq
  rw [hq, torusLatticePeriodization_eq_representative _ hG q]

/-- Under the no-wrap hypothesis for the Laplacian, the stored Laplacian is the quotient
periodization of the whole-plane Laplacian in `L²`. -/
theorem cutoff_laplacian_eq_periodizationL2 (F : SchwartzMap WholePlane ℂ)
    (hG : SupportedInIocFundamentalBox
      ((schwartzLaplacian F : SchwartzMap WholePlane ℂ) : WholePlane → ℂ)) :
    transverseScalarLInfToL2 (cutoff F).laplacian =
      torusLatticePeriodizationL2 (schwartzLaplacian F) hG := by
  apply transverseScalarL2_ext_coeff
  intro q
  rw [cutoff_laplacian_coeff, transverseScalarCoeff_torusLatticePeriodizationL2]
  exact (fourierSample_schwartzLaplacian F q).symm

/-- Almost-everywhere representative form of the stored Laplacian identification. -/
theorem cutoff_laplacian_ae_representative (F : SchwartzMap WholePlane ℂ)
    (hG : SupportedInIocFundamentalBox
      ((schwartzLaplacian F : SchwartzMap WholePlane ℂ) : WholePlane → ℂ)) :
    ((cutoff F).laplacian : TransverseTorus → ℂ) =ᵐ[transverseMeasure]
      fun q ↦ (schwartzLaplacian F) (wholePlaneIocRepresentative q) := by
  have hinclude := transverseScalarLInfToL2_coe_ae (cutoff F).laplacian
  have hperiod := torusLatticePeriodizationL2_coe_ae (schwartzLaplacian F) hG
  rw [cutoff_laplacian_eq_periodizationL2 F hG] at hinclude
  filter_upwards [hinclude.symm.trans hperiod] with q hq
  rw [hq, torusLatticePeriodization_eq_representative _ hG q]

/-! ## Sup-norm bounds -/

/-- The `L∞` norm of the completed value is bounded by any pointwise bound for the bump. -/
theorem norm_cutoff_value_le (F : SchwartzMap WholePlane ℂ)
    (hF : SupportedInIocFundamentalBox (F : WholePlane → ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖F x‖ ≤ C) :
    ‖(cutoff F).value‖ ≤ C := by
  apply norm_transverseScalarLInf_le_of_ae_bound _ hC
  filter_upwards [cutoff_value_ae_representative F hF] with q hq
  rw [hq]
  exact hbound _

/-- The `L∞` norm of one stored gradient component is bounded by any pointwise bound for the
corresponding whole-plane coordinate derivative. -/
theorem norm_cutoff_gradient_le (F : SchwartzMap WholePlane ℂ) (j : Fin 2)
    (hG : SupportedInIocFundamentalBox
      ((∂_{wholePlaneBasis j} F : SchwartzMap WholePlane ℂ) : WholePlane → ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖(∂_{wholePlaneBasis j} F) x‖ ≤ C) :
    ‖(cutoff F).gradient j‖ ≤ C := by
  apply norm_transverseScalarLInf_le_of_ae_bound _ hC
  filter_upwards [cutoff_gradient_ae_representative F j hG] with q hq
  rw [hq]
  exact hbound _

/-- The `L∞` norm of the stored Laplacian is bounded by any pointwise bound for the
whole-plane Laplacian of the bump. -/
theorem norm_cutoff_laplacian_le (F : SchwartzMap WholePlane ℂ)
    (hG : SupportedInIocFundamentalBox
      ((schwartzLaplacian F : SchwartzMap WholePlane ℂ) : WholePlane → ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖(schwartzLaplacian F) x‖ ≤ C) :
    ‖(cutoff F).laplacian‖ ≤ C := by
  apply norm_transverseScalarLInf_le_of_ae_bound _ hC
  filter_upwards [cutoff_laplacian_ae_representative F hG] with q hq
  rw [hq]
  exact hbound _

/-! ## Real profiles -/

/-- A compactly supported smooth real profile, complexified as a Schwartz function. -/
def realSchwartz (f : WholePlane → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) : SchwartzMap WholePlane ℂ :=
  (hc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hf)

/-- The complexified profile evaluates to the complexification of the profile. -/
@[simp] theorem realSchwartz_apply (f : WholePlane → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (x : WholePlane) :
    realSchwartz f hf hc x = ((f x : ℝ) : ℂ) :=
  rfl

/-- One coordinate derivative of a complexified real profile is the complexification of the
profile's coordinate derivative. -/
theorem lineDerivOp_realSchwartz_apply (f : WholePlane → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (j : Fin 2) (x : WholePlane) :
    (∂_{wholePlaneBasis j} (realSchwartz f hf hc)) x =
      ((ConstantCoefficientBackground.realProfileCoordinateDerivative f j x : ℝ) : ℂ) := by
  have hd : HasFDerivAt (fun y ↦ ((f y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ f x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt
  have hcoe : ((realSchwartz f hf hc : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) =
      fun y ↦ ((f y : ℝ) : ℂ) := rfl
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hcoe, hd.fderiv]
  rfl

/-- Complexification does not change the norm of an iterated derivative. -/
theorem norm_iteratedFDeriv_realSchwartz (f : WholePlane → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (i : ℕ) (x : WholePlane) :
    ‖iteratedFDeriv ℝ i ((realSchwartz f hf hc : SchwartzMap WholePlane ℂ) :
        WholePlane → ℂ) x‖ =
      ‖iteratedFDeriv ℝ i f x‖ := by
  have hcomp : ((realSchwartz f hf hc : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) =
      (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ f := rfl
  rw [hcomp]
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf.contDiffAt
    (by exact_mod_cast le_top)

/-- Each repeated coordinate derivative of a Schwartz bump is a second iterated derivative in
that coordinate direction. -/
theorem lineDerivOp_lineDerivOp_eq_iteratedFDeriv (F : SchwartzMap WholePlane ℂ)
    (j : Fin 2) (x : WholePlane) :
    (∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F)) x =
      iteratedFDeriv ℝ 2 (F : WholePlane → ℂ) x (fun _ ↦ wholePlaneBasis j) :=
  SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv (n := 2)
    (m := fun _ : Fin 2 ↦ wholePlaneBasis j) (f := F) (x := x)

/-- Pointwise bound for the Laplacian of a Schwartz bump in terms of the operator norm of its
second derivative: the two coordinate directions are unit vectors. -/
theorem norm_schwartzLaplacian_apply_le (F : SchwartzMap WholePlane ℂ) {C : ℝ}
    (hbound : ∀ x, ‖iteratedFDeriv ℝ 2 (F : WholePlane → ℂ) x‖ ≤ C) (x : WholePlane) :
    ‖(schwartzLaplacian F) x‖ ≤ 2 * C := by
  have hterm : ∀ j : Fin 2,
      ‖(∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F)) x‖ ≤ C := by
    intro j
    rw [lineDerivOp_lineDerivOp_eq_iteratedFDeriv]
    calc
      ‖iteratedFDeriv ℝ 2 (F : WholePlane → ℂ) x (fun _ ↦ wholePlaneBasis j)‖ ≤
          ‖iteratedFDeriv ℝ 2 (F : WholePlane → ℂ) x‖ *
            ∏ _i : Fin 2, ‖wholePlaneBasis j‖ :=
        (iteratedFDeriv ℝ 2 (F : WholePlane → ℂ) x).le_opNorm _
      _ = ‖iteratedFDeriv ℝ 2 (F : WholePlane → ℂ) x‖ := by
        simp [wholePlaneBasis]
      _ ≤ C := hbound x
  calc
    ‖(schwartzLaplacian F) x‖ =
        ‖∑ j : Fin 2, (∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F)) x‖ := by
      rw [schwartzLaplacian_apply]
    _ ≤ ∑ j : Fin 2, ‖(∂_{wholePlaneBasis j} (∂_{wholePlaneBasis j} F)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, C := Finset.sum_le_sum fun j _ ↦ hterm j
    _ = 2 * C := by simp [Finset.sum_const]

end SchwartzPeriodicCutoff

end

end FastDynamo

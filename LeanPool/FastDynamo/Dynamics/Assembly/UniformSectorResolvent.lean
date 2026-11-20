/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.ProductWeakDerivative
public import LeanPool.FastDynamo.Operator.FixedSectorLowerOrderDecay
public import LeanPool.FastDynamo.Fourier.ProductH2

/-!
# Axially uniform fixed-sector resolvent bounds

The fixed-sector modules `FastDynamo.Operator.FixedSectorDiffusionInverse` and
`FastDynamo.Operator.FixedSectorLowerOrderDecay` construct, for one axial
frequency `K`, the diffusion inverse `D_K(σ)` and a Neumann threshold beyond
which the reduced operator `A_{ε,K}` has a resolvent.  Both the threshold and
the `H²` bound they produce degrade as `|K| → ∞`: the axial transport term
carries the factor `‖axialMultiplier K‖ = 2π|K|`, and the fixed-sector lift
`axialLiftH2 K` is only `fixedKWeightBound K = 1 + (2πK)²`-bounded.

This module removes both `K`-dependencies.  Two scalar estimates do all the
work:

* the *product-weight elliptic gain*
  `productH2Weight_le_diffusion_bound_times_symbol`, the analogue for the full
  three-dimensional weight `productH2Weight n K` of the transverse gain already
  used to land the diffusion inverse in `H²`, with the same `K`-free constant
  `σ⁻¹ + ε⁻¹`;
* the *AM–GM axial bound* `norm_axialMultiplier_mul_inverseSymbol_le`, which
  absorbs the factor `2π|K|` of the axial transport into the diffusion symbol
  at the cost of `(2√(εσ))⁻¹`, again `K`-free.

From them the module derives a lower-order bound
`norm_reducedInductionLowerOrder_comp_diffusionInverse_le` whose right-hand
side does not mention `K`, a single threshold
`exists_uniform_sigma_norm_lowerOrder_comp_diffusionInverse_le_half`
valid simultaneously for every axial sector, and finally the uniform graph
estimate `norm_axialLiftH2_le_graph`:

`∃ C > 0, ∀ K b, ‖axialLiftH2 K b‖ ≤ C * (‖ι b‖ + ‖A_{ε,K} b‖)`,

which is what an assembly of the sector resolvents into a product-space
resolvent needs in order to see the lifted `H²` certificates as a square
summable family.

## Contents

* **Scalar cores.** `productH2Weight_le_diffusion_bound_times_symbol`,
  `norm_axialMultiplier_mul_inverseSymbol_le`.
* **The lifted diffusion inverse.** The product-weighted multiplier
  `productWeightedDiffusionInverseCoeffMultiplier`, its `ℓ²` map, and the
  `K`-uniform certificate bound
  `norm_productH2WeightedCoeffs_axialLiftH2_diffusionInverse_le`.
* **`K`-uniform lower-order bounds.** The axial multiplier
  `reducedInductionAxialInverseCoeffMultiplier` and its map, the axial
  termwise bound `norm_reducedInductionAxialTransport_comp_diffusionInverse_le`,
  the assembled bound `uniformLowerOrderDiffusionInverseBound` with
  `norm_reducedInductionLowerOrder_comp_diffusionInverse_le`, its decay, and
  `exists_uniform_sigma_norm_lowerOrder_comp_diffusionInverse_le_half`.
* **The uniform graph estimate.**
  `norm_reducedInductionLowerOrder_apply_le_of_comp_le_half`,
  `norm_axialLiftH2_le_of_comp_le_half` and `norm_axialLiftH2_le_graph`.

## Relation to the `expRay` chain of `FixedSectorLowerOrderDecay.lean`

Only the *axial* transport bound is proved here: the transverse-transport and stretching
bounds are already `K`-free, and are consumed here as the public
`norm_reducedInductionTransport_comp_inverse_le` and
`norm_reducedInductionStretching_comp_inverse_le` of
`FastDynamo/Operator/FixedSectorLowerOrderDecay.lean` rather than restated.

The `K`-uniform axial bound sits **beside** that module's exponential-ray
chain: `eventually_hasResolventOn_reducedInductionOperator_expRay` there carries a
`K`-dependent threshold, which is all the fixed-sector half-plane resolvent
(`FastDynamo/Global/ReducedInductionHalfPlaneResolvent.lean`, and everything the
main theorem routes through it) needs, so two Neumann thresholds coexist.  The
assembly needs a threshold valid *simultaneously* for every `K`, which the
fixed-sector chain does not provide; so the uniform threshold is built here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The two scalar cores -/

/--
**Product-weight elliptic gain.**  For positive `ε` and `σ` the full
three-dimensional order-two weight `productH2Weight n K` is dominated by
`(σ⁻¹ + ε⁻¹)` times the fixed-sector diffusion-pencil symbol.  The constant
does not depend on the axial frequency `K`, which is what makes the lifted
`H²` certificate of the diffusion inverse uniformly bounded.
-/
theorem productH2Weight_le_diffusion_bound_times_symbol
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (K : ℤ) (n : TransverseFrequency) :
    productH2Weight n K ≤ (σ⁻¹ + ε⁻¹) *
      reducedInductionDiffusionPencilSymbol ε σ K n := by
  unfold productH2Weight reducedInductionDiffusionPencilSymbol
    transverseFrequencyEnergy fixedSectorAxialEnergy
  have hE : (0:ℝ) ≤ ∑ j, (n j : ℝ) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hK : (0:ℝ) ≤ ((K : ℝ)) ^ 2 := sq_nonneg _
  have hpi : (0:ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have hW : (0:ℝ) ≤ 2 ^ 2 * Real.pi ^ 2 * (∑ j, (n j : ℝ) ^ 2 + (K:ℝ) ^ 2) := by positivity
  field_simp
  nlinarith [hW, mul_pos hε hσ, sq_nonneg ε, sq_nonneg σ, mul_nonneg hW (sq_nonneg ε)]

/--
**AM–GM axial bound.**  The axial transport multiplier `2π|K|` composed with
the diffusion inverse symbol is bounded by `(2√(εσ))⁻¹`, uniformly in the axial
frequency `K` and the transverse frequency `n`: the denominator
`σ + ε(2πK)² + ε|2πn|²` already dominates `2 · 2π|K| √(εσ)`.
-/
theorem norm_axialMultiplier_mul_inverseSymbol_le
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (K : ℤ) (n : TransverseFrequency) :
    ‖axialMultiplier K‖ * reducedInductionDiffusionInverseSymbol ε σ K n ≤
      (2 * Real.sqrt (ε * σ))⁻¹ := by
  have hden : 0 < reducedInductionDiffusionPencilSymbol ε σ K n :=
    reducedInductionDiffusionPencilSymbol_pos hε.le hσ K n
  have hs : 0 < Real.sqrt (ε * σ) := Real.sqrt_pos.2 (by positivity)
  rw [norm_axialMultiplier, reducedInductionDiffusionInverseSymbol, ← div_eq_mul_inv,
    div_le_iff₀ hden, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  have hE : (0:ℝ) ≤ transverseFrequencyEnergy n := transverseFrequencyEnergy_nonneg n
  have hsqσ : Real.sqrt σ ^ 2 = σ := Real.sq_sqrt hσ.le
  have hsqε : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hprod : Real.sqrt ε * Real.sqrt σ = Real.sqrt (ε * σ) := (Real.sqrt_mul hε.le σ).symm
  have hAK : fixedSectorAxialEnergy K = (2 * Real.pi * |(K:ℝ)|) ^ 2 := by
    unfold fixedSectorAxialEnergy
    rw [show (2 * Real.pi * |(K:ℝ)|) ^ 2 = (2 * Real.pi) ^ 2 * |(K:ℝ)| ^ 2 by ring, sq_abs]
    ring
  have key : 0 ≤ (Real.sqrt σ - Real.sqrt ε * (2 * Real.pi * |(K:ℝ)|)) ^ 2 := sq_nonneg _
  unfold reducedInductionDiffusionPencilSymbol
  rw [hAK]
  nlinarith [mul_nonneg hε.le hE, key, hs.le, Real.sqrt_nonneg ε, Real.sqrt_nonneg σ,
    mul_nonneg (Real.sqrt_nonneg ε) (Real.sqrt_nonneg σ),
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) Real.pi_pos.le) (abs_nonneg ((K:ℝ)))]

/-! ## The diffusion inverse seen from the lifted product sector -/

/--
A vector of a finite `PiLp 2` product is bounded by `C` times a vector of another such product as
soon as this holds in every component: the sum of the squared componentwise bounds is exactly the
square of the claimed bound.
-/
private theorem norm_piLp_two_le_of_components {ι : Type*} [Fintype ι]
    (E : ι → Type*) (F : ι → Type*)
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, SeminormedAddCommGroup (F i)]
    (v : PiLp 2 E) (w : PiLp 2 F) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖v i‖ ≤ C * ‖w i‖) :
    ‖v‖ ≤ C * ‖w‖ := by
  have hsq : ‖v‖ ^ 2 ≤ (C * ‖w‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i, ‖v i‖ ^ 2 ≤ ∑ i, (C * ‖w i‖) ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
      _ = C ^ 2 * ∑ i, ‖w i‖ ^ 2 := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
      _ = C ^ 2 * ‖w‖ ^ 2 := by rw [PiLp.norm_sq_eq_of_L2]
      _ = (C * ‖w‖) ^ 2 := by ring
  nlinarith [norm_nonneg v, mul_nonneg hC (norm_nonneg w)]

/--
The diffusion-inverse multiplier carrying the *product* order-two weight `productH2Weight n K`.
This is the multiplier of the certificate stored by the fixed-sector lift `axialLiftH2 K` of the
diffusion inverse.
-/
def productWeightedDiffusionInverseCoeffMultiplier
    (ε σ : ℝ) (K : ℤ) (n : TransverseFrequency) : ℂ :=
  (productH2Weight n K : ℂ) *
    reducedInductionDiffusionInverseCoeffMultiplier ε σ K n

/--
The product-weighted diffusion-inverse multiplier is bounded by `σ⁻¹ + ε⁻¹`, uniformly in the
transverse frequency *and* in the axial frequency `K`; this is the elliptic gain
`productH2Weight_le_diffusion_bound_times_symbol` in multiplier form.
-/
theorem norm_productWeightedDiffusionInverseCoeffMultiplier_le
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (K : ℤ) (n : TransverseFrequency) :
    ‖productWeightedDiffusionInverseCoeffMultiplier ε σ K n‖ ≤ σ⁻¹ + ε⁻¹ := by
  simp only [productWeightedDiffusionInverseCoeffMultiplier,
    reducedInductionDiffusionInverseCoeffMultiplier, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (productH2Weight_pos n K),
    abs_of_nonneg (reducedInductionDiffusionInverseSymbol_nonneg hε.le hσ K n)]
  have hd : 0 < reducedInductionDiffusionPencilSymbol ε σ K n :=
    reducedInductionDiffusionPencilSymbol_pos hε.le hσ K n
  have hbound := productH2Weight_le_diffusion_bound_times_symbol hε hσ K n
  change productH2Weight n K * reducedInductionDiffusionInverseSymbol ε σ K n ≤ σ⁻¹ + ε⁻¹
  rw [reducedInductionDiffusionInverseSymbol, ← div_eq_mul_inv]
  exact (div_le_iff₀ hd).2 (by simpa [mul_comm] using hbound)

/-- The `ℓ²` coefficient map of the product-weighted diffusion inverse. -/
def productWeightedDiffusionInverseCoeffMap
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ)
      (productWeightedDiffusionInverseCoeffMultiplier ε σ K n))
    (by positivity)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (productWeightedDiffusionInverseCoeffMultiplier ε σ K n)).trans
        (norm_productWeightedDiffusionInverseCoeffMultiplier_le hε hσ K n))

/--
The product-weighted coefficient map acts diagonally, multiplying the `n`-th coefficient by
`productWeightedDiffusionInverseCoeffMultiplier ε σ K n`.
-/
@[simp] theorem productWeightedDiffusionInverseCoeffMap_apply
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    productWeightedDiffusionInverseCoeffMap ε σ K hε hσ a n =
      productWeightedDiffusionInverseCoeffMultiplier ε σ K n * a n :=
  rfl

/--
Operator-norm form of the elliptic gain: the product-weighted diffusion-inverse coefficient map
has norm at most `σ⁻¹ + ε⁻¹`, with no dependence on the axial sector.
-/
theorem norm_productWeightedDiffusionInverseCoeffMap_le
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    ‖productWeightedDiffusionInverseCoeffMap ε σ K hε hσ‖ ≤ σ⁻¹ + ε⁻¹ := by
  exact lp.norm_mapCLM_le 2 _ (by positivity)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (productWeightedDiffusionInverseCoeffMultiplier ε σ K n)).trans
        (norm_productWeightedDiffusionInverseCoeffMultiplier_le hε hσ K n))

/--
Converting the stored transverse certificate of the diffusion inverse into the product `H²`
certificate multiplies by the weight ratio, and the result is exactly the product-weighted
coefficient map.
-/
theorem fixedKRatioCoeffMap_reducedInductionDiffusionInverseWeightedCoeffMap
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (a : TransverseScalarFourierL2) :
    fixedKRatioCoeffMap K
        (reducedInductionDiffusionInverseWeightedCoeffMap ε σ K hε hσ a) =
      productWeightedDiffusionInverseCoeffMap ε σ K hε hσ a := by
  apply lp.ext
  funext n
  change fixedKWeightRatio K n *
      (reducedInductionDiffusionInverseWeightedCoeffMultiplier ε σ K n * a n) =
    productWeightedDiffusionInverseCoeffMultiplier ε σ K n * a n
  rw [reducedInductionDiffusionInverseWeightedCoeffMultiplier,
    productWeightedDiffusionInverseCoeffMultiplier, ← mul_assoc, ← mul_assoc,
    fixedKWeightRatio_mul_transverseWeight]

/--
Insertion at a single axial frequency is an `ℓ²` isometry onto its range, so the scalar weighted
lift has exactly the norm of the weight-ratio conversion it inserts.
-/
theorem norm_fixedKScalarWeightedLift (K : ℤ) (y : TransverseScalarFourierL2) :
    ‖fixedKScalarWeightedLift K y‖ = ‖fixedKRatioCoeffMap K y‖ := by
  have h : fixedKScalarWeightedLift K y =
      lp.single (E := fun _ : ℤ => TransverseScalarFourierL2) 2 K
        (fixedKRatioCoeffMap K y) := rfl
  rw [h, lp.norm_single (by norm_num)]

/--
**`K`-uniform certificate bound.**  The product `H²` certificate of the lifted diffusion inverse
is bounded by `(σ⁻¹ + ε⁻¹)` times the datum, up to the fixed norm of the transverse Fourier
analysis, exactly as the fixed-sector estimates of
`FastDynamo.Operator.FixedSectorLowerOrderDecay` carry that constant.  The bound does not depend
on the axial sector `K`, unlike the generic bound of the lift `axialLiftH2 K`, whose constant is
`1 + (2πK)²`.
-/
theorem norm_productH2WeightedCoeffs_axialLiftH2_diffusionInverse_le
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) (f : TransverseC3L2) :
    ‖productH2WeightedCoeffs
        (axialLiftH2 K (reducedInductionDiffusionInverse ε σ K hε hσ f))‖ ≤
      (σ⁻¹ + ε⁻¹) * (‖transverseC3FourierAnalysis‖ * ‖f‖) := by
  rw [productH2WeightedCoeffs_axialLiftH2]
  have hcomp : ∀ i : Fin 3,
      ‖fixedKWeightedLift K
          (transverseH2WeightedCoeffs
            (reducedInductionDiffusionInverse ε σ K hε hσ f)) i‖ ≤
        (σ⁻¹ + ε⁻¹) * ‖transverseC3FourierAnalysis f i‖ := by
    intro i
    have h1 : fixedKWeightedLift K
        (transverseH2WeightedCoeffs
          (reducedInductionDiffusionInverse ε σ K hε hσ f)) i =
        fixedKScalarWeightedLift K
          (reducedInductionDiffusionInverseWeightedCoeffMap ε σ K hε hσ
            (transverseC3FourierAnalysis f i)) := rfl
    rw [h1, norm_fixedKScalarWeightedLift,
      fixedKRatioCoeffMap_reducedInductionDiffusionInverseWeightedCoeffMap]
    exact (productWeightedDiffusionInverseCoeffMap ε σ K hε hσ).le_of_opNorm_le
      (norm_productWeightedDiffusionInverseCoeffMap_le ε σ K hε hσ) _
  calc
    ‖fixedKWeightedLift K
        (transverseH2WeightedCoeffs
          (reducedInductionDiffusionInverse ε σ K hε hσ f))‖ ≤
        (σ⁻¹ + ε⁻¹) * ‖transverseC3FourierAnalysis f‖ :=
      norm_piLp_two_le_of_components _ _ _ _ (by positivity) hcomp
    _ ≤ (σ⁻¹ + ε⁻¹) * (‖transverseC3FourierAnalysis‖ * ‖f‖) := by
      have hnonneg : (0:ℝ) ≤ σ⁻¹ + ε⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left
        (transverseC3FourierAnalysis.le_opNorm f) hnonneg

/-! ## The axially uniform lower-order estimates -/

/--
The scalar Fourier multiplier of the axial transport term after the diffusion inverse: the axial
wavenumber `2πiK` times the inverse diffusion symbol.
-/
def reducedInductionAxialInverseCoeffMultiplier
    (ε σ : ℝ) (K : ℤ) (n : TransverseFrequency) : ℂ :=
  axialMultiplier K * reducedInductionDiffusionInverseCoeffMultiplier ε σ K n

/--
**AM–GM in multiplier form.**  The axial-transport multiplier after the diffusion inverse is
bounded by `(2√(εσ))⁻¹` at every transverse frequency, uniformly in the axial frequency `K`.
This is the estimate that removes the factor `‖axialMultiplier K‖ = 2π|K|` from the fixed-sector
Neumann threshold.
-/
theorem norm_reducedInductionAxialInverseCoeffMultiplier_le
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (K : ℤ) (n : TransverseFrequency) :
    ‖reducedInductionAxialInverseCoeffMultiplier ε σ K n‖ ≤
      (2 * Real.sqrt (ε * σ))⁻¹ := by
  rw [reducedInductionAxialInverseCoeffMultiplier, norm_mul,
    reducedInductionDiffusionInverseCoeffMultiplier, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (reducedInductionDiffusionInverseSymbol_nonneg hε.le hσ K n)]
  exact norm_axialMultiplier_mul_inverseSymbol_le hε hσ K n

/-- The `ℓ²` coefficient map of the axial transport after the diffusion inverse. -/
def reducedInductionAxialInverseCoeffMap
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ)
      (reducedInductionAxialInverseCoeffMultiplier ε σ K n))
    (by positivity)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (reducedInductionAxialInverseCoeffMultiplier ε σ K n)).trans
        (norm_reducedInductionAxialInverseCoeffMultiplier_le hε hσ K n))

/--
The axial coefficient map acts diagonally, multiplying the `n`-th coefficient by
`reducedInductionAxialInverseCoeffMultiplier ε σ K n`.
-/
@[simp] theorem reducedInductionAxialInverseCoeffMap_apply
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    reducedInductionAxialInverseCoeffMap ε σ K hε hσ a n =
      reducedInductionAxialInverseCoeffMultiplier ε σ K n * a n :=
  rfl

/-- Operator-norm form of the AM–GM bound: the axial coefficient map has norm at most
`(2√(εσ))⁻¹`, with no dependence on the axial sector. -/
theorem norm_reducedInductionAxialInverseCoeffMap_le
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    ‖reducedInductionAxialInverseCoeffMap ε σ K hε hσ‖ ≤
      (2 * Real.sqrt (ε * σ))⁻¹ := by
  exact lp.norm_mapCLM_le 2 _ (by positivity)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (reducedInductionAxialInverseCoeffMultiplier ε σ K n)).trans
        (norm_reducedInductionAxialInverseCoeffMultiplier_le hε hσ K n))

/--
The axial wavenumber times the diffusion inverse, read back in physical `L²`, is exactly the
vector Fourier multiplier with symbol `reducedInductionAxialInverseCoeffMap ε σ K`.  Keeping the
factor `axialMultiplier K` inside the symbol is what makes the resulting bound `K`-uniform.
-/
theorem axialMultiplier_smul_transverseH2Embedding_comp_diffusionInverse_eq
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    axialMultiplier K •
        transverseH2Embedding.comp
          (reducedInductionDiffusionInverse ε σ K hε hσ) =
      transverseC3FourierMultiplier
        (reducedInductionAxialInverseCoeffMap ε σ K hε hσ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply transverseC3L2_ext_coeff
  intro n i
  rw [smul_apply, map_smul, smul_eq_mul,
    ContinuousLinearMap.comp_apply,
    transverseCoeff_reducedInductionDiffusionInverse,
    transverseCoeff_transverseC3FourierMultiplier,
    reducedInductionAxialInverseCoeffMap_apply,
    transverseC3FourierAnalysisCoeff,
    reducedInductionAxialInverseCoeffMultiplier, mul_assoc]

/--
**`K`-uniform axial transport bound.**  The axial transport term composed with the diffusion
inverse is `O((εσ)^{-1/2})` with a constant depending only on `u`, not on the axial sector.  The
repository bound `FixedSectorLowerOrderDecay` proves instead carries the factor
`‖axialMultiplier K‖ = 2π|K|`.
-/
theorem norm_reducedInductionAxialTransport_comp_diffusionInverse_le
    (u : TransverseRealW1Inf) (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    ‖(reducedInductionAxialTransport u K).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ)‖ ≤
      ‖scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf 2 u)‖ *
        (‖transverseC3FourierSynthesis‖ *
          ((2 * Real.sqrt (ε * σ))⁻¹ * ‖transverseC3FourierAnalysis‖)) := by
  have hfac : (reducedInductionAxialTransport u K).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ) =
      (scalarVectorMulTransverse
        (transverseW1InfComplexValueCoordLInf 2 u)).comp
        (axialMultiplier K •
          transverseH2Embedding.comp
            (reducedInductionDiffusionInverse ε σ K hε hσ)) := by
    ext f
    simp [reducedInductionAxialTransport, ContinuousLinearMap.comp_assoc]
  rw [hfac, axialMultiplier_smul_transverseH2Embedding_comp_diffusionInverse_eq]
  calc
    ‖(scalarVectorMulTransverse
        (transverseW1InfComplexValueCoordLInf 2 u)).comp
        (transverseC3FourierMultiplier
          (reducedInductionAxialInverseCoeffMap ε σ K hε hσ))‖ ≤
        ‖scalarVectorMulTransverse
            (transverseW1InfComplexValueCoordLInf 2 u)‖ *
          ‖transverseC3FourierMultiplier
            (reducedInductionAxialInverseCoeffMap ε σ K hε hσ)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖scalarVectorMulTransverse
            (transverseW1InfComplexValueCoordLInf 2 u)‖ *
          (‖transverseC3FourierSynthesis‖ *
            ((2 * Real.sqrt (ε * σ))⁻¹ * ‖transverseC3FourierAnalysis‖)) := by
      gcongr
      calc
        ‖transverseC3FourierMultiplier
            (reducedInductionAxialInverseCoeffMap ε σ K hε hσ)‖ ≤
            ‖transverseC3FourierSynthesis‖ *
              (‖reducedInductionAxialInverseCoeffMap ε σ K hε hσ‖ *
                ‖transverseC3FourierAnalysis‖) :=
          norm_transverseC3FourierMultiplier_le _
        _ ≤ ‖transverseC3FourierSynthesis‖ *
            ((2 * Real.sqrt (ε * σ))⁻¹ * ‖transverseC3FourierAnalysis‖) := by
          gcongr
          exact norm_reducedInductionAxialInverseCoeffMap_le ε σ K hε hσ

/--
The axially uniform bound for the lower-order correction through the diffusion inverse: the sum
of the transverse-transport, axial-transport and stretching bounds, each with a constant
depending only on the velocity `u` and on `ε`, `σ`.
-/
def uniformLowerOrderDiffusionInverseBound
    (u : TransverseRealW1Inf) (ε σ : ℝ) : ℝ :=
  (∑ j : Fin 2,
      ‖scalarVectorMulTransverse
        (transverseW1InfComplexValueCoordLInf j.castSucc u)‖) *
      (‖transverseC3FourierSynthesis‖ *
        (Real.sqrt ((4 * ε * σ)⁻¹) * ‖transverseC3FourierAnalysis‖)) +
    ‖scalarVectorMulTransverse
        (transverseW1InfComplexValueCoordLInf 2 u)‖ *
      (‖transverseC3FourierSynthesis‖ *
        ((2 * Real.sqrt (ε * σ))⁻¹ * ‖transverseC3FourierAnalysis‖)) +
    (∑ j : Fin 2, ‖vectorScalarMulTransverse
        (transverseW1InfComplexDerivLInf j u)‖ *
        ‖transverseCoordL2 j.castSucc‖) *
      (‖transverseC3FourierSynthesis‖ *
        (σ⁻¹ * ‖transverseC3FourierAnalysis‖))

/--
**The `K`-uniform lower-order bound.**  For every axial sector `K` the lower-order correction
composed with the fixed-sector diffusion inverse is bounded by
`uniformLowerOrderDiffusionInverseBound u ε σ`, a quantity that does not mention `K`.
-/
theorem norm_reducedInductionLowerOrder_comp_diffusionInverse_le
    (u : TransverseRealW1Inf) (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    ‖(reducedInductionLowerOrder u K).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ)‖ ≤
      uniformLowerOrderDiffusionInverseBound u ε σ := by
  refine (norm_reducedInductionLowerOrder_comp_le u K
    (reducedInductionDiffusionInverse ε σ K hε hσ)).trans ?_
  unfold uniformLowerOrderDiffusionInverseBound
  exact add_le_add
    (add_le_add
      (norm_reducedInductionTransport_comp_inverse_le u ε σ K hε hσ)
      (norm_reducedInductionAxialTransport_comp_diffusionInverse_le
        u ε σ K hε hσ))
    (norm_reducedInductionStretching_comp_inverse_le u ε σ K hε hσ)

/-- The uniform lower-order bound tends to zero as the spectral parameter grows. -/
theorem tendsto_uniformLowerOrderDiffusionInverseBound_atTop
    (u : TransverseRealW1Inf) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun σ : ℝ => uniformLowerOrderDiffusionInverseBound u ε σ)
      Filter.atTop (nhds 0) := by
  have hlin : Filter.Tendsto (fun σ : ℝ => 4 * ε * σ)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop (by positivity)
  have h1 : Filter.Tendsto (fun σ : ℝ => Real.sqrt ((4 * ε * σ)⁻¹))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hlin).sqrt
  have hεσ : Filter.Tendsto (fun σ : ℝ => ε * σ)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop hε
  have h2 : Filter.Tendsto (fun σ : ℝ => (2 * Real.sqrt (ε * σ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      ((Real.tendsto_sqrt_atTop.comp hεσ).const_mul_atTop (by norm_num))
  have h3 : Filter.Tendsto (fun σ : ℝ => σ⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have g1 := (((h1.mul_const ‖transverseC3FourierAnalysis‖).const_mul
    ‖transverseC3FourierSynthesis‖).const_mul
      (∑ j : Fin 2, ‖scalarVectorMulTransverse
        (transverseW1InfComplexValueCoordLInf j.castSucc u)‖))
  have g2 := (((h2.mul_const ‖transverseC3FourierAnalysis‖).const_mul
    ‖transverseC3FourierSynthesis‖).const_mul
      ‖scalarVectorMulTransverse
        (transverseW1InfComplexValueCoordLInf 2 u)‖)
  have g3 := (((h3.mul_const ‖transverseC3FourierAnalysis‖).const_mul
    ‖transverseC3FourierSynthesis‖).const_mul
      (∑ j : Fin 2, ‖vectorScalarMulTransverse
        (transverseW1InfComplexDerivLInf j u)‖ *
        ‖transverseCoordL2 j.castSucc‖))
  have hsum := (g1.add g2).add g3
  unfold uniformLowerOrderDiffusionInverseBound
  simpa using hsum

/--
**One threshold for all axial sectors.**  Beyond an explicit spectral parameter `σ`, which can be
taken larger than any prescribed `c`, the lower-order correction composed with the fixed-sector
diffusion inverse has norm at most `1/2` *simultaneously in every axial sector* `K`.  The
repository threshold of `FastDynamo.Operator.FixedSectorLowerOrderDecay` is attained only
sector by sector, because the axial transport bound it uses carries the factor `2π|K|`.
-/
theorem exists_uniform_sigma_norm_lowerOrder_comp_diffusionInverse_le_half
    (u : TransverseRealW1Inf) {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ∃ (σ : ℝ) (hσ : 0 < σ), c < σ ∧ ∀ K : ℤ,
      ‖(reducedInductionLowerOrder u K).comp
        (reducedInductionDiffusionInverse ε σ K hε hσ)‖ ≤ 1 / 2 := by
  have hsmall : ∀ᶠ σ : ℝ in Filter.atTop,
      uniformLowerOrderDiffusionInverseBound u ε σ < 1 / 2 :=
    (tendsto_order.1
      (tendsto_uniformLowerOrderDiffusionInverseBound_atTop u hε)).2
      (1 / 2) (by norm_num)
  obtain ⟨σ, hbound, hc, hpos⟩ :=
    (hsmall.and ((Filter.eventually_gt_atTop c).and
      (Filter.eventually_gt_atTop (0 : ℝ)))).exists
  refine ⟨σ, hpos, hc, fun K => ?_⟩
  exact (norm_reducedInductionLowerOrder_comp_diffusionInverse_le
    u ε σ K hε hpos).trans hbound.le

/-! ## The uniform graph estimate -/

/--
The graph norm of a product `H²` element is the maximum of the norms of its physical field and of
its stored certificate, so a bound on it is exactly a pair of bounds.
-/
theorem norm_productH2_le_iff (V : ProductC3H2) (c : ℝ) :
    ‖V‖ ≤ c ↔
      ‖productH2Embedding V‖ ≤ c ∧ ‖productH2WeightedCoeffs V‖ ≤ c := by
  change ‖(productH2Embedding V, productH2WeightedCoeffs V)‖ ≤ c ↔ _
  rw [Prod.norm_def, max_le_iff]

/--
Under the uniform Neumann bound of
`exists_uniform_sigma_norm_lowerOrder_comp_diffusionInverse_le_half`, the lower-order part of the
reduced action is dominated by the full reduced pencil at `σ`, with constant one.  This is the
step that converts a bound on `L_K D_K(σ)` into an a priori bound on `L_K` itself.
-/
theorem norm_reducedInductionLowerOrder_apply_le_of_comp_le_half
    (u : TransverseRealW1Inf) (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (hhalf : ‖(reducedInductionLowerOrder u K).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ)‖ ≤ 1 / 2)
    (b : TransverseC3H2) :
    ‖reducedInductionLowerOrder u K b‖ ≤
      ‖(reducedInductionOperator u ε K).pencil (σ : ℂ) b‖ := by
  have hb : reducedInductionDiffusionInverse ε σ K hε hσ
      (reducedInductionDiffusionPencil ε K (σ : ℂ) b) = b := by
    simpa using ContinuousLinearMap.ext_iff.1
      (inverse_comp_reducedInductionDiffusionPencil ε σ K hε hσ) b
  have hsplit : reducedInductionDiffusionPencil ε K (σ : ℂ) b =
      (reducedInductionOperator u ε K).pencil (σ : ℂ) b +
        reducedInductionLowerOrder u K b := by
    have h := ContinuousLinearMap.ext_iff.1
      (reducedInductionPencil_eq_diffusionPencil_sub_lowerOrder u ε K (σ : ℂ)) b
    rw [sub_apply] at h
    rw [h]
    abel
  have hL : ‖reducedInductionLowerOrder u K b‖ ≤
      1 / 2 * ‖reducedInductionDiffusionPencil ε K (σ : ℂ) b‖ := by
    have hcomp : reducedInductionLowerOrder u K b =
        ((reducedInductionLowerOrder u K).comp
          (reducedInductionDiffusionInverse ε σ K hε hσ))
          (reducedInductionDiffusionPencil ε K (σ : ℂ) b) := by
      rw [ContinuousLinearMap.comp_apply, hb]
    rw [hcomp]
    exact ((reducedInductionLowerOrder u K).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ)).le_of_opNorm_le hhalf _
  have htri : ‖reducedInductionDiffusionPencil ε K (σ : ℂ) b‖ ≤
      ‖(reducedInductionOperator u ε K).pencil (σ : ℂ) b‖ +
        ‖reducedInductionLowerOrder u K b‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  linarith

/--
The same hypothesis bounds the *diffusion* pencil by twice the full reduced pencil: the
lower-order part can be moved to the right-hand side.
-/
theorem norm_reducedInductionDiffusionPencil_apply_le_of_comp_le_half
    (u : TransverseRealW1Inf) (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (hhalf : ‖(reducedInductionLowerOrder u K).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ)‖ ≤ 1 / 2)
    (b : TransverseC3H2) :
    ‖reducedInductionDiffusionPencil ε K (σ : ℂ) b‖ ≤
      2 * ‖(reducedInductionOperator u ε K).pencil (σ : ℂ) b‖ := by
  have hsplit : reducedInductionDiffusionPencil ε K (σ : ℂ) b =
      (reducedInductionOperator u ε K).pencil (σ : ℂ) b +
        reducedInductionLowerOrder u K b := by
    have h := ContinuousLinearMap.ext_iff.1
      (reducedInductionPencil_eq_diffusionPencil_sub_lowerOrder u ε K (σ : ℂ)) b
    rw [sub_apply] at h
    rw [h]
    abel
  have hL := norm_reducedInductionLowerOrder_apply_le_of_comp_le_half
    u ε σ K hε hσ hhalf b
  have htri : ‖reducedInductionDiffusionPencil ε K (σ : ℂ) b‖ ≤
      ‖(reducedInductionOperator u ε K).pencil (σ : ℂ) b‖ +
        ‖reducedInductionLowerOrder u K b‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  linarith

/-- The reduced pencil at a positive real parameter is bounded by the graph data of its
argument. -/
theorem norm_reducedInductionPencil_apply_le
    (u : TransverseRealW1Inf) (ε σ : ℝ) (K : ℤ) (hσ : 0 < σ)
    (b : TransverseC3H2) :
    ‖(reducedInductionOperator u ε K).pencil (σ : ℂ) b‖ ≤
      σ * ‖transverseH2Embedding b‖ + ‖reducedInductionAction u ε K b‖ := by
  have hp : (reducedInductionOperator u ε K).pencil (σ : ℂ) b =
      (σ : ℂ) • transverseH2Embedding b - reducedInductionAction u ε K b := rfl
  rw [hp]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]

/--
**The uniform `H²` estimate at one threshold.**  If the uniform Neumann bound holds at `σ`, the
fixed-sector lift of any transverse amplitude is bounded by an explicit `K`-free constant times
the graph norm `‖ι b‖ + ‖A_{ε,K} b‖`.  Compare the generic lift bound, whose constant
`1 + (2πK)²` blows up with the axial sector.
-/
theorem norm_axialLiftH2_le_of_comp_le_half
    (u : TransverseRealW1Inf) (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (hhalf : ‖(reducedInductionLowerOrder u K).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ)‖ ≤ 1 / 2)
    (b : TransverseC3H2) :
    ‖axialLiftH2 K b‖ ≤
      (1 + 2 * (σ⁻¹ + ε⁻¹) * ‖transverseC3FourierAnalysis‖ * (σ + 1)) *
        (‖transverseH2Embedding b‖ + ‖reducedInductionAction u ε K b‖) := by
  have hx : (0:ℝ) ≤ ‖transverseH2Embedding b‖ := norm_nonneg _
  have hy : (0:ℝ) ≤ ‖reducedInductionAction u ε K b‖ := norm_nonneg _
  have hA : (0:ℝ) ≤ ‖transverseC3FourierAnalysis‖ := norm_nonneg _
  have hw : (0:ℝ) < σ⁻¹ + ε⁻¹ := by positivity
  have hCone : (1:ℝ) ≤
      1 + 2 * (σ⁻¹ + ε⁻¹) * ‖transverseC3FourierAnalysis‖ * (σ + 1) := by
    have hprod : (0:ℝ) ≤
        2 * (σ⁻¹ + ε⁻¹) * ‖transverseC3FourierAnalysis‖ * (σ + 1) :=
      mul_nonneg (mul_nonneg (by linarith) hA) (by linarith)
    linarith
  have hpencil := norm_reducedInductionPencil_apply_le u ε σ K hσ b
  have hdiff := norm_reducedInductionDiffusionPencil_apply_le_of_comp_le_half
    u ε σ K hε hσ hhalf b
  have hg : ‖reducedInductionDiffusionPencil ε K (σ : ℂ) b‖ ≤
      2 * (σ * ‖transverseH2Embedding b‖ +
        ‖reducedInductionAction u ε K b‖) := by
    linarith
  have hb : reducedInductionDiffusionInverse ε σ K hε hσ
      (reducedInductionDiffusionPencil ε K (σ : ℂ) b) = b := by
    simpa using ContinuousLinearMap.ext_iff.1
      (inverse_comp_reducedInductionDiffusionPencil ε σ K hε hσ) b
  rw [norm_productH2_le_iff]
  constructor
  · rw [productH2Embedding_axialLiftH2, norm_axialLiftFromH2]
    nlinarith
  · have hcert : productH2WeightedCoeffs (axialLiftH2 K b) =
        productH2WeightedCoeffs (axialLiftH2 K
          (reducedInductionDiffusionInverse ε σ K hε hσ
            (reducedInductionDiffusionPencil ε K (σ : ℂ) b))) := by
      rw [hb]
    rw [hcert]
    calc
      ‖productH2WeightedCoeffs (axialLiftH2 K
          (reducedInductionDiffusionInverse ε σ K hε hσ
            (reducedInductionDiffusionPencil ε K (σ : ℂ) b)))‖ ≤
          (σ⁻¹ + ε⁻¹) * (‖transverseC3FourierAnalysis‖ *
            ‖reducedInductionDiffusionPencil ε K (σ : ℂ) b‖) :=
        norm_productH2WeightedCoeffs_axialLiftH2_diffusionInverse_le
          ε σ K hε hσ _
      _ ≤ (σ⁻¹ + ε⁻¹) * (‖transverseC3FourierAnalysis‖ *
            (2 * (σ * ‖transverseH2Embedding b‖ +
              ‖reducedInductionAction u ε K b‖))) := by
        gcongr
      _ ≤ (1 + 2 * (σ⁻¹ + ε⁻¹) * ‖transverseC3FourierAnalysis‖ * (σ + 1)) *
            (‖transverseH2Embedding b‖ +
              ‖reducedInductionAction u ε K b‖) := by
        nlinarith [mul_nonneg (mul_nonneg hw.le hA) hx,
          mul_nonneg (mul_nonneg hw.le hA) hy, hσ.le,
          mul_nonneg (mul_nonneg (mul_nonneg hw.le hA) hσ.le) hy,
          mul_nonneg (mul_nonneg hw.le hA) (add_nonneg hx hy)]

/--
**(U), the uniform graph estimate.**  There is a constant `C = C(u, ε) > 0`, *independent of the
axial sector* `K`, with

`‖axialLiftH2 K b‖ ≤ C * (‖ι b‖ + ‖A_{ε,K} b‖)`

for every transverse `H²` amplitude `b`.  This is what lets the fixed-sector `H²` certificates be
assembled into a square-summable family over the axial frequencies, and hence the sector
resolvents into a product-space resolvent; the naive lift bound has the `K`-dependent constant
`1 + (2πK)²`.
-/
theorem norm_axialLiftH2_le_graph
    (u : TransverseRealW1Inf) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℤ) (b : TransverseC3H2),
      ‖axialLiftH2 K b‖ ≤
        C * (‖transverseH2Embedding b‖ + ‖reducedInductionAction u ε K b‖) := by
  obtain ⟨σ, hσ, _, hhalf⟩ :=
    exists_uniform_sigma_norm_lowerOrder_comp_diffusionInverse_le_half u hε 0
  refine ⟨1 + 2 * (σ⁻¹ + ε⁻¹) * ‖transverseC3FourierAnalysis‖ * (σ + 1),
    ?_, fun K b => ?_⟩
  · have hw : (0:ℝ) < σ⁻¹ + ε⁻¹ := by positivity
    have hA : (0:ℝ) ≤ ‖transverseC3FourierAnalysis‖ := norm_nonneg _
    have hprod : (0:ℝ) ≤
        2 * (σ⁻¹ + ε⁻¹) * ‖transverseC3FourierAnalysis‖ * (σ + 1) :=
      mul_nonneg (mul_nonneg (by linarith) hA) (by linarith)
    linarith
  · exact norm_axialLiftH2_le_of_comp_le_half u ε σ K hε hσ (hhalf K) b

end

end FastDynamo

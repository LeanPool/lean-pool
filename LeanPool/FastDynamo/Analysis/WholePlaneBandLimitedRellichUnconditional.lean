/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneBandLimitedRellich
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Lemmas

/-!
# Scalar local Rellich on the whole plane

The spectral-isolation step of the paper (§2.3) quotes Rellich's theorem for the restriction
of `H¹(ℝ²)` to a bounded disc containing the support of the velocity.
`WholePlaneBandLimitedRellich` reduces that statement to compactness of the concrete
coefficient-level time--frequency concentration maps.  This module proves those maps compact, so
local Rellich holds for every finite-measure set with no compactness hypothesis left.

The route is a Hilbert--Schmidt argument.  Mathlib's inverse Fourier transform of an `L¹`
class and its inverse Plancherel transform of an `L²` class are first shown to have the same
almost-everywhere representative, which turns the quotient-level band-limited synthesis into a
classical inverse-Fourier integral.  Abstractly, an `L²` family `g` of Hilbert-valued sections
induces the bounded operator `f ↦ (x ↦ ⟪g x, f⟫)`, and this operator is compact because simple
sections give finite sums of rank-one operators.  Taking `g` to be the spatially truncated
frequency kernel identifies the band-limited restriction with such an operator.

## Contents

* Compatibility of inverse Fourier representatives on `L¹ ∩ L²`.
* Pointwise integral representation of the band-limited synthesis: the compactly supported
  `L¹ ∩ L²` coefficient and its inverse-Fourier integral representation.
* Compactness from finite sums of rank-one operators.
* Compact operators from square-integrable Hilbert-valued sections.
* Compactness of the whole-plane band-limited restriction: frequency kernel sections, dependence
  on the spatial parameter, the spatially truncated Hilbert-valued section, the inner-product
  identification, and the operator identity with its compactness corollary.
* Scalar local Rellich on the whole plane: the finite-measure specialization.
-/

@[expose] public section

/-!
## Compatibility of inverse Fourier representatives on `L¹ ∩ L²`

Mathlib exposes the inverse Fourier transform of an `L¹` class as a bounded
continuous function and the inverse Plancherel transform of an `L²` class as
another `L²` class.  This part proves that the two representatives agree
almost everywhere when the input classes have the same representative.

The statement is specialized to the scalar whole-plane setting needed by the
band-limited local Rellich argument.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap

/-- Multiplication form of the multiplication formula: for integrable `f` and `g` the
inverse Fourier transform may be moved from one factor to the other under the integral,
`∫ 𝓕⁻f · g = ∫ f · 𝓕⁻g`. -/
private theorem wholePlane_integral_fourierInv_mul_eq
    (f g : WholePlane → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ x : WholePlane, 𝓕⁻ f x * g x =
      ∫ x : WholePlane, f x * 𝓕⁻ g x := by
  simpa [Real.fourierInv_eq, VectorFourier.fourierIntegral,
    real_inner_comm] using
    (VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ)
      (e := Real.fourierChar) (L := -innerₗ WholePlane)
      Real.continuous_fourierChar continuous_inner.neg hf hg)

/-- The inverse Plancherel transform and the pointwise inverse-Fourier
integral give the same almost-everywhere representative on a scalar input
which belongs to both `L²` and `L¹`.

The equality hypothesis is representative-level: it is the
interface produced by compact frequency truncation of an `L²` coefficient.
-/
theorem wholePlane_fourierSynthesis_ae_eq_fourierTransformInv
    (f₂ : WholePlaneScalarL2)
    (f₁ : Lp ℂ 1 (volume : Measure WholePlane))
    (h₁₂ : (f₁ : WholePlane → ℂ) =ᵐ[volume]
      (f₂ : WholePlane → ℂ)) :
    (wholePlaneFourierSynthesis ℂ f₂ : WholePlane → ℂ) =ᵐ[volume]
      (Real.Lp.fourierTransformInv f₁ : WholePlane → ℂ) := by
  let u : WholePlaneScalarL2 := wholePlaneFourierSynthesis ℂ f₂
  let q : WholePlane → ℂ :=
    (Real.Lp.fourierTransformInv f₁ : WholePlane → ℂ)
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp u).locallyIntegrable (by norm_num)
  · exact (Real.Lp.fourierTransformInv f₁).continuous.locallyIntegrable
  · intro g hgSmooth hgCompact
    let gℂ : WholePlane → ℂ := Complex.ofRealCLM ∘ g
    have hgℂSmooth := Complex.ofRealCLM.contDiff.comp hgSmooth
    have hgℂCompact : HasCompactSupport gℂ :=
      hgCompact.comp_left rfl
    let φ : SchwartzMap WholePlane ℂ :=
      hgℂCompact.toSchwartzMap hgℂSmooth
    have hdist := congrArg
      (fun T : TemperedDistribution WholePlane ℂ ↦ T φ)
      (fourierInv_wholePlaneL2ToTempered ℂ f₂)
    have hf₁int : Integrable (f₁ : WholePlane → ℂ) :=
      L1.integrable_coeFn f₁
    have hφint : Integrable (φ : WholePlane → ℂ) := φ.integrable
    have hfubini := wholePlane_integral_fourierInv_mul_eq
      (f₁ : WholePlane → ℂ) (φ : WholePlane → ℂ) hf₁int hφint
    change (∫ x : WholePlane, (g x : ℂ) * (u x : ℂ) ∂volume) =
      ∫ x : WholePlane, (g x : ℂ) * q x ∂volume
    change (∫ x : WholePlane, φ x * (u x : ℂ) ∂volume) =
      ∫ x : WholePlane, φ x * q x ∂volume
    have hdist' :
        (∫ x : WholePlane, φ x * (u x : ℂ) ∂volume) =
          ∫ x : WholePlane,
            𝓕⁻ (φ : WholePlane → ℂ) x * (f₂ x : ℂ) ∂volume := by
      simpa [u, wholePlaneL2ToTempered_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply,
        TemperedDistribution.fourierInv_apply,
        SchwartzMap.fourierInv_coe] using hdist.symm
    rw [hdist']
    calc
      (∫ x : WholePlane,
          𝓕⁻ (φ : WholePlane → ℂ) x * (f₂ x : ℂ) ∂volume) =
          ∫ x : WholePlane,
            𝓕⁻ (φ : WholePlane → ℂ) x * (f₁ x : ℂ) ∂volume := by
        apply integral_congr_ae
        filter_upwards [h₁₂] with x hx
        rw [← hx]
      _ = ∫ x : WholePlane,
          (f₁ x : ℂ) * 𝓕⁻ (φ : WholePlane → ℂ) x ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = ∫ x : WholePlane, 𝓕⁻ (f₁ : WholePlane → ℂ) x * φ x ∂volume := hfubini.symm
      _ = ∫ x : WholePlane, φ x * q x ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        rw [mul_comm]
        simp [q]

end

end FastDynamo

/-!
## Pointwise integral representation of the band-limited synthesis

This part packages the compactly frequency-supported coefficient occurring
in `wholePlaneH1LowFrequencyFromCoeff` as an `L¹` class.  The inverse
Plancherel representative bridge then identifies the quotient-level
`L²` synthesis with its classical inverse-Fourier integral almost everywhere.

No integral-operator or compactness construction is introduced here.  Those
belong to the finite-rank kernel approximation layer below.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

/-! ## The compactly supported `L¹ ∩ L²` coefficient -/

/-- Pointwise representative of the low-frequency inverse-Bessel coefficient.

The representative of `c` is the canonical coercion from its `L²` class.
The multiplier vanishes outside `Metric.ball 0 R`, including the degenerate
case `R ≤ 0` where it vanishes everywhere. -/
def wholePlaneH1LowFrequencyCoeffFn
    (R : ℝ) (c : WholePlaneScalarL2) (xi : WholePlane) : ℂ :=
  h1LowFrequencyRecoverMass R xi * c xi

/-- The quotient-level `L²` multiplier has the expected compactly supported
pointwise representative. -/
theorem scalarVectorMulL2_h1LowFrequencyRecoverMass_coe_ae
    (R : ℝ) (c : WholePlaneScalarL2) :
    (scalarVectorMulL2 (E := ℂ) volume
        (h1LowFrequencyRecoverMassLInf R) c : WholePlane → ℂ) =ᵐ[volume]
      wholePlaneH1LowFrequencyCoeffFn R c := by
  filter_upwards [
    scalarVectorMulL2_coe_ae (E := ℂ) volume
      (h1LowFrequencyRecoverMassLInf R) c,
    h1LowFrequencyRecoverMassLInf_coe_ae R]
    with xi hmul hsymbol
  rw [hmul, hsymbol]
  rfl

/-- The pointwise low-frequency coefficient belongs to `L²`. -/
theorem wholePlaneH1LowFrequencyCoeffFn_memLp_two
    (R : ℝ) (c : WholePlaneScalarL2) :
    MemLp (wholePlaneH1LowFrequencyCoeffFn R c) 2 volume := by
  exact (Lp.memLp (scalarVectorMulL2 (E := ℂ) volume
    (h1LowFrequencyRecoverMassLInf R) c)).ae_eq
      (scalarVectorMulL2_h1LowFrequencyRecoverMass_coe_ae R c)

/-- The pointwise low-frequency coefficient vanishes at every frequency with `R ≤ ‖ξ‖`, so
it is supported in the closed ball of radius `R`. -/
theorem wholePlaneH1LowFrequencyCoeffFn_eq_zero_of_norm_ge
    (R : ℝ) (c : WholePlaneScalarL2) (xi : WholePlane)
    (hxi : R ≤ ‖xi‖) :
    wholePlaneH1LowFrequencyCoeffFn R c xi = 0 := by
  simp [wholePlaneH1LowFrequencyCoeffFn,
    h1LowFrequencyRecoverMass, hxi]

/-- Compact frequency support upgrades the low-frequency coefficient from
`L²` to `L¹`. -/
theorem wholePlaneH1LowFrequencyCoeffFn_memLp_one
    (R : ℝ) (c : WholePlaneScalarL2) :
    MemLp (wholePlaneH1LowFrequencyCoeffFn R c) 1 volume := by
  exact (wholePlaneH1LowFrequencyCoeffFn_memLp_two R c).mono_exponent_of_measure_support_ne_top
      (s := Metric.ball (0 : WholePlane) R)
      (fun xi hxi ↦
        wholePlaneH1LowFrequencyCoeffFn_eq_zero_of_norm_ge R c xi (by
          simpa [Metric.mem_ball, dist_zero_right, not_lt] using hxi))
      measure_ball_lt_top.ne (by norm_num)

/-- The canonical `L¹` class of the compactly supported low-frequency
coefficient. -/
def wholePlaneH1LowFrequencyCoeffL1
    (R : ℝ) (c : WholePlaneScalarL2) :
    Lp ℂ 1 (volume : Measure WholePlane) :=
  (wholePlaneH1LowFrequencyCoeffFn_memLp_one R c).toLp _

/-- The `L¹` class of the low-frequency coefficient has the pointwise coefficient function
as an almost everywhere representative. -/
theorem wholePlaneH1LowFrequencyCoeffL1_coe_ae
    (R : ℝ) (c : WholePlaneScalarL2) :
    (wholePlaneH1LowFrequencyCoeffL1 R c : WholePlane → ℂ) =ᵐ[volume]
      wholePlaneH1LowFrequencyCoeffFn R c := by
  exact MemLp.coeFn_toLp _

/-- The canonical `L¹` truncation and the quotient-level `L²`
multiplier use the same representative almost everywhere. -/
theorem wholePlaneH1LowFrequencyCoeffL1_ae_eq_L2
    (R : ℝ) (c : WholePlaneScalarL2) :
    (wholePlaneH1LowFrequencyCoeffL1 R c : WholePlane → ℂ) =ᵐ[volume]
      (scalarVectorMulL2 (E := ℂ) volume
        (h1LowFrequencyRecoverMassLInf R) c : WholePlane → ℂ) :=
  (wholePlaneH1LowFrequencyCoeffL1_coe_ae R c).trans
    (scalarVectorMulL2_h1LowFrequencyRecoverMass_coe_ae R c).symm

/-! ## Inverse-Fourier integral representation -/

/-- The scalar low-frequency synthesis agrees almost everywhere with the
bounded continuous inverse Fourier transform of its canonical `L¹`
coefficient. -/
theorem wholePlaneH1LowFrequencyFromCoeff_ae_eq_fourierTransformInv
    (R : ℝ) (c : WholePlaneScalarL2) :
    (wholePlaneH1LowFrequencyFromCoeff ℂ R c : WholePlane → ℂ) =ᵐ[volume]
      (Real.Lp.fourierTransformInv
        (wholePlaneH1LowFrequencyCoeffL1 R c) : WholePlane → ℂ) := by
  change (wholePlaneFourierSynthesis ℂ
    (scalarVectorMulL2 (E := ℂ) volume
      (h1LowFrequencyRecoverMassLInf R) c) : WholePlane → ℂ) =ᵐ[volume] _
  exact wholePlane_fourierSynthesis_ae_eq_fourierTransformInv
    (scalarVectorMulL2 (E := ℂ) volume
      (h1LowFrequencyRecoverMassLInf R) c)
    (wholePlaneH1LowFrequencyCoeffL1 R c)
    (wholePlaneH1LowFrequencyCoeffL1_ae_eq_L2 R c)

/-- Equivalent formulation using the inverse Fourier transform of the
pointwise compactly supported coefficient. -/
theorem wholePlaneH1LowFrequencyFromCoeff_ae_eq_fourierInv
    (R : ℝ) (c : WholePlaneScalarL2) :
    (wholePlaneH1LowFrequencyFromCoeff ℂ R c : WholePlane → ℂ) =ᵐ[volume]
      𝓕⁻ (wholePlaneH1LowFrequencyCoeffFn R c) := by
  filter_upwards [
    wholePlaneH1LowFrequencyFromCoeff_ae_eq_fourierTransformInv R c]
    with x hx
  calc
    (wholePlaneH1LowFrequencyFromCoeff ℂ R c : WholePlane → ℂ) x =
        Real.Lp.fourierTransformInv
          (wholePlaneH1LowFrequencyCoeffL1 R c) x := hx
    _ = 𝓕⁻
        (wholePlaneH1LowFrequencyCoeffL1 R c : WholePlane → ℂ) x :=
      Real.Lp.fourierTransformInv_apply _ _
    _ = 𝓕⁻ (wholePlaneH1LowFrequencyCoeffFn R c) x :=
      Real.fourierInv_congr_ae
        (wholePlaneH1LowFrequencyCoeffL1_coe_ae R c) x

/-- Explicit inverse-Fourier integral formula for the quotient-level
band-limited synthesis.  The first two factors form the scalar kernel; this
module does not package its sections as `L²` vectors. -/
theorem wholePlaneH1LowFrequencyFromCoeff_ae_eq_integral
    (R : ℝ) (c : WholePlaneScalarL2) :
    ∀ᵐ x ∂volume,
      (wholePlaneH1LowFrequencyFromCoeff ℂ R c : WholePlane → ℂ) x =
        ∫ xi : WholePlane,
          (Real.fourierChar (inner ℝ xi x) : ℂ) *
            h1LowFrequencyRecoverMass R xi * c xi := by
  filter_upwards [wholePlaneH1LowFrequencyFromCoeff_ae_eq_fourierInv R c]
    with x hx
  rw [hx, Real.fourierInv_eq]
  simp only [Circle.smul_def, smul_eq_mul,
    wholePlaneH1LowFrequencyCoeffFn, mul_assoc]

end

end FastDynamo

/-!
## Compactness from finite sums of rank-one operators

This part isolates the functional-analytic core of the finite-rank route to
compactness.  A rank-one operator is compact because it factors through the
locally compact scalar field.  Hence finite sums of rank-one operators are
compact, and any operator that can be approximated arbitrarily well in
operator norm by such sums is compact.

The last theorem is phrased with a varying `Fin n` index.  This is convenient
for simple-kernel approximations: scalar coefficients can be absorbed into
the output vector of each rank-one summand, so no separate coefficient family
is needed.
-/

namespace FastDynamo

noncomputable section

open Filter

variable {K E H : Type*} [RCLike K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup H] [InnerProductSpace K H]

/-- A rank-one operator from a Hilbert space is compact.

The proof records the useful factorization
`H -> K -> E`: the inner-product functional has locally compact codomain,
and postcomposition by the scalar-to-vector map preserves compactness. -/
theorem isCompactOperator_rankOne (x : E) (y : H) :
    IsCompactOperator (InnerProductSpace.rankOne K x y) := by
  let _ : ProperSpace K := FiniteDimensional.proper_rclike K K
  rw [InnerProductSpace.rankOne_def']
  exact
    (isCompactOperator_of_locallyCompactSpace_dom
      (innerSL K y)).clm_comp
      (ContinuousLinearMap.toSpanSingleton K x)

/-- A list sum of rank-one operators is compact.  This form is convenient
when a simple-function induction appends the summands arising from two
disjoint pieces. -/
theorem isCompactOperator_list_sum_rankOne
    (L : List (E × H)) :
    IsCompactOperator
      ((L.map fun xy ↦
        InnerProductSpace.rankOne K xy.1 xy.2).sum) := by
  induction L with
  | nil =>
      simpa using
        (isCompactOperator_zero :
          IsCompactOperator (0 : H →L[K] E))
  | cons xy L ih =>
      simpa [List.map_cons, List.sum_cons] using
        (isCompactOperator_rankOne (K := K) xy.1 xy.2).add ih

/-- List-indexed rank-one approximation criterion for compactness. -/
theorem isCompactOperator_of_list_rankOne_approximation
    [CompleteSpace E] (T : H →L[K] E)
    (happrox : ∀ ε > 0, ∃ L : List (E × H),
      ‖(L.map (fun xy ↦
        InnerProductSpace.rankOne K xy.1 xy.2)).sum - T‖ < ε) :
    IsCompactOperator T := by
  apply (isClosed_setOfPred_isCompactOperator :
    IsClosed {A : H →L[K] E | IsCompactOperator A}).closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases happrox ε hε with ⟨L, hL⟩
  refine ⟨(L.map fun xy ↦
    InnerProductSpace.rankOne K xy.1 xy.2).sum, ?_, ?_⟩
  · exact isCompactOperator_list_sum_rankOne (K := K) L
  · simpa only [dist_eq_norm, norm_sub_rev] using hL

end

end FastDynamo

/-!
## Compact operators from square-integrable Hilbert-valued sections

Let `g : L²(α; H)`.  The pointwise inner products

`f ↦ (x ↦ ⟪g x, f⟫)`

define a bounded operator `H → L²(α)` with norm at most `‖g‖`.  We prove that
this operator is compact.  The proof approximates `g` by finite-range simple
functions; an indicator section gives exactly one rank-one operator, and
addition concatenates the finite lists of summands.

This is the abstract Hilbert--Schmidt step needed by the band-limited Rellich
argument.  A concrete integral kernel `k(x, ξ)` is used by taking
`g(x) = conj (k(x, ·))` in the coefficient Hilbert space.  Identifying the
resulting pointwise inner product with inverse Fourier synthesis is the
subject of the next part.
-/

namespace FastDynamo

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

variable {α K H : Type*} [MeasurableSpace α] [RCLike K]
  [NormedAddCommGroup H] [InnerProductSpace K H]

/-- Apply a square-integrable `H`-valued section pointwise as an inner-product
functional. -/
def l2SectionApply (μ : Measure α) (g : Lp H 2 μ) (f : H) :
    Lp K 2 μ :=
  ((Lp.memLp g).inner_const (𝕜 := K) f).toLp
    (fun x ↦ inner K (g x) f)

/-- The `L²` class `l2SectionApply μ g f` is represented almost everywhere by the pointwise inner
product `x ↦ ⟪g x, f⟫`. -/
theorem l2SectionApply_coe_ae (μ : Measure α)
    (g : Lp H 2 μ) (f : H) :
    (l2SectionApply (K := K) μ g f : α → K) =ᵐ[μ]
      fun x ↦ inner K (g x) f := by
  exact MemLp.coeFn_toLp _

/-- Pointwise pairing against a fixed section is additive in the vector argument, because the
inner product is additive in its second slot. -/
theorem l2SectionApply_add (μ : Measure α)
    (g : Lp H 2 μ) (f₁ f₂ : H) :
    l2SectionApply (K := K) μ g (f₁ + f₂) =
      l2SectionApply (K := K) μ g f₁ +
        l2SectionApply (K := K) μ g f₂ := by
  apply Lp.ext
  filter_upwards [
    l2SectionApply_coe_ae (K := K) μ g (f₁ + f₂),
    l2SectionApply_coe_ae (K := K) μ g f₁,
    l2SectionApply_coe_ae (K := K) μ g f₂,
    Lp.coeFn_add (l2SectionApply (K := K) μ g f₁)
      (l2SectionApply (K := K) μ g f₂)]
    with x hsum h₁ h₂ hadd
  rw [hsum, hadd, Pi.add_apply, h₁, h₂, inner_add_right]

/-- Pointwise pairing against a fixed section is homogeneous in the vector argument: a scalar in
the second inner-product slot comes out unchanged. -/
theorem l2SectionApply_smul (μ : Measure α)
    (g : Lp H 2 μ) (c : K) (f : H) :
    l2SectionApply (K := K) μ g (c • f) =
      c • l2SectionApply (K := K) μ g f := by
  apply Lp.ext
  filter_upwards [
    l2SectionApply_coe_ae (K := K) μ g (c • f),
    l2SectionApply_coe_ae (K := K) μ g f,
    Lp.coeFn_smul c (l2SectionApply (K := K) μ g f)]
    with x hleft hright hsmul
  rw [hleft, hsmul, Pi.smul_apply, hright, inner_smul_right,
    smul_eq_mul]

/-- Cauchy--Schwarz applied pointwise: the `L²` norm of `x ↦ ⟪g x, f⟫` is at most `‖g‖ * ‖f‖`. -/
theorem norm_l2SectionApply_le (μ : Measure α)
    (g : Lp H 2 μ) (f : H) :
    ‖l2SectionApply (K := K) μ g f‖ ≤ ‖g‖ * ‖f‖ := by
  calc
    ‖l2SectionApply (K := K) μ g f‖ ≤ ‖f‖ * ‖g‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [l2SectionApply_coe_ae (K := K) μ g f] with x hx
      rw [hx]
      simpa only [mul_comm] using norm_inner_le_norm (g x) f
    _ = ‖g‖ * ‖f‖ := mul_comm _ _

/-- The operator associated with a square-integrable Hilbert-valued section. -/
def l2SectionOperator (μ : Measure α) (g : Lp H 2 μ) :
    H →L[K] Lp K 2 μ :=
  LinearMap.mkContinuous
    { toFun := l2SectionApply (K := K) μ g
      map_add' := l2SectionApply_add (K := K) μ g
      map_smul' := l2SectionApply_smul (K := K) μ g }
    ‖g‖ (norm_l2SectionApply_le (K := K) μ g)

/-- The bundled continuous linear map acts by the pointwise pairing `l2SectionApply μ g`. -/
@[simp]
theorem l2SectionOperator_apply (μ : Measure α)
    (g : Lp H 2 μ) (f : H) :
    l2SectionOperator (K := K) μ g f =
      l2SectionApply (K := K) μ g f :=
  rfl

/-- The image of `f` under the section operator is represented almost everywhere by the pointwise
inner product `x ↦ ⟪g x, f⟫`. -/
theorem l2SectionOperator_apply_coe_ae (μ : Measure α)
    (g : Lp H 2 μ) (f : H) :
    (l2SectionOperator (K := K) μ g f : α → K) =ᵐ[μ]
      fun x ↦ inner K (g x) f :=
  l2SectionApply_coe_ae (K := K) μ g f

/-- The operator built from a square-integrable section `g` has operator norm at most `‖g‖`. -/
theorem norm_l2SectionOperator_le (μ : Measure α)
    (g : Lp H 2 μ) :
    ‖l2SectionOperator (K := K) μ g‖ ≤ ‖g‖ := by
  exact (l2SectionOperator (K := K) μ g).opNorm_le_bound
    (norm_nonneg g) (norm_l2SectionApply_le (K := K) μ g)

/-- The pairing is additive in the section: pairing against `g₁ - g₂` gives the difference of the
two pairings. -/
theorem l2SectionApply_sub_left (μ : Measure α)
    (g₁ g₂ : Lp H 2 μ) (f : H) :
    l2SectionApply (K := K) μ (g₁ - g₂) f =
      l2SectionApply (K := K) μ g₁ f -
        l2SectionApply (K := K) μ g₂ f := by
  apply Lp.ext
  filter_upwards [
    l2SectionApply_coe_ae (K := K) μ (g₁ - g₂) f,
    l2SectionApply_coe_ae (K := K) μ g₁ f,
    l2SectionApply_coe_ae (K := K) μ g₂ f,
    Lp.coeFn_sub g₁ g₂,
    Lp.coeFn_sub (l2SectionApply (K := K) μ g₁ f)
      (l2SectionApply (K := K) μ g₂ f)]
    with x hleft h₁ h₂ hgsub houtsub
  rw [hleft, hgsub, houtsub, Pi.sub_apply, Pi.sub_apply,
    h₁, h₂, inner_sub_left]

/-- The pairing is additive in the section: pairing against `g₁ + g₂` gives the sum of the two
pairings. -/
theorem l2SectionApply_add_left (μ : Measure α)
    (g₁ g₂ : Lp H 2 μ) (f : H) :
    l2SectionApply (K := K) μ (g₁ + g₂) f =
      l2SectionApply (K := K) μ g₁ f +
        l2SectionApply (K := K) μ g₂ f := by
  apply Lp.ext
  filter_upwards [
    l2SectionApply_coe_ae (K := K) μ (g₁ + g₂) f,
    l2SectionApply_coe_ae (K := K) μ g₁ f,
    l2SectionApply_coe_ae (K := K) μ g₂ f,
    Lp.coeFn_add g₁ g₂,
    Lp.coeFn_add (l2SectionApply (K := K) μ g₁ f)
      (l2SectionApply (K := K) μ g₂ f)]
    with x hleft h₁ h₂ hgadd houtadd
  rw [hleft, hgadd, houtadd, Pi.add_apply, Pi.add_apply,
    h₁, h₂, inner_add_left]

/-- The assignment section `↦` operator is additive: the operator of `g₁ + g₂` is the sum of the
two operators. -/
theorem l2SectionOperator_add (μ : Measure α)
    (g₁ g₂ : Lp H 2 μ) :
    l2SectionOperator (K := K) μ (g₁ + g₂) =
      l2SectionOperator (K := K) μ g₁ +
        l2SectionOperator (K := K) μ g₂ := by
  apply ContinuousLinearMap.ext
  intro f
  exact l2SectionApply_add_left (K := K) μ g₁ g₂ f

/-- The assignment section `↦` operator commutes with differences: the operator of `g₁ - g₂` is
the difference of the two operators. -/
theorem l2SectionOperator_sub (μ : Measure α)
    (g₁ g₂ : Lp H 2 μ) :
    l2SectionOperator (K := K) μ (g₁ - g₂) =
      l2SectionOperator (K := K) μ g₁ -
        l2SectionOperator (K := K) μ g₂ := by
  apply ContinuousLinearMap.ext
  intro f
  exact l2SectionApply_sub_left (K := K) μ g₁ g₂ f

/-- Two sections at `L²` distance `‖g₁ - g₂‖` give operators at most that far apart in operator
norm. -/
theorem norm_l2SectionOperator_sub_le (μ : Measure α)
    (g₁ g₂ : Lp H 2 μ) :
    ‖l2SectionOperator (K := K) μ g₁ -
        l2SectionOperator (K := K) μ g₂‖ ≤ ‖g₁ - g₂‖ := by
  rw [← l2SectionOperator_sub (K := K)]
  exact norm_l2SectionOperator_le (K := K) μ (g₁ - g₂)

/-- A section constant on a finite-measure set gives exactly a rank-one
operator. -/
theorem l2SectionOperator_indicatorConst (μ : Measure α)
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (y : H) :
    l2SectionOperator (K := K) μ (indicatorConstLp 2 hs hμs y) =
      InnerProductSpace.rankOne K
        (indicatorConstLp 2 hs hμs (1 : K)) y := by
  apply ContinuousLinearMap.ext
  intro f
  rw [InnerProductSpace.rankOne_apply]
  apply Lp.ext
  filter_upwards [
    l2SectionOperator_apply_coe_ae (K := K) μ
      (indicatorConstLp 2 hs hμs y) f,
    @indicatorConstLp_coeFn α H _ 2 μ _ s hs hμs y,
    @indicatorConstLp_coeFn α K _ 2 μ _ s hs hμs (1 : K),
    Lp.coeFn_smul (inner K y f)
      (indicatorConstLp 2 hs hμs (1 : K))]
    with x hleft hy hone hsmul
  rw [hleft, hy, hsmul, Pi.smul_apply, hone]
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

/-- The operator associated with an `Lp` simple section is exactly a finite
list sum of rank-one operators. -/
theorem exists_list_l2SectionOperator_eq_sum_rankOne
    (μ : Measure α) (g : Lp.simpleFunc H 2 μ) :
    ∃ L : List ((Lp K 2 μ) × H),
      l2SectionOperator (K := K) μ (g : Lp H 2 μ) =
        (L.map fun xy ↦
          InnerProductSpace.rankOne K xy.1 xy.2).sum := by
  refine Lp.simpleFunc.induction (p := (2 : ℝ≥0∞))
    (α := α) (E := H) two_ne_zero ENNReal.ofNat_ne_top ?_ ?_ g
  · intro y s hs hμs
    refine ⟨[(indicatorConstLp 2 hs hμs.ne (1 : K), y)], ?_⟩
    rw [Lp.simpleFunc.coe_indicatorConst,
      l2SectionOperator_indicatorConst (K := K) μ hs hμs.ne y]
    simp
  · intro f₁ f₂ hf₁ hf₂ _ h₁ h₂
    rcases h₁ with ⟨L₁, hL₁⟩
    rcases h₂ with ⟨L₂, hL₂⟩
    refine ⟨L₁ ++ L₂, ?_⟩
    rw [show ((↑(SimpleFunc.toLp f₁ hf₁ +
          SimpleFunc.toLp f₂ hf₂) : Lp H 2 μ)) =
        (↑(SimpleFunc.toLp f₁ hf₁) : Lp H 2 μ) +
          (↑(SimpleFunc.toLp f₂ hf₂) : Lp H 2 μ) by rfl,
      l2SectionOperator_add (K := K), hL₁, hL₂, List.map_append,
      List.sum_append]

/-- Quantitative finite-rank approximation of the section operator.  For
each tolerance, simple-function density supplies a finite list of rank-one
summands within that tolerance in operator norm. -/
theorem exists_list_rankOne_approx_l2SectionOperator
    (μ : Measure α) (g : Lp H 2 μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : List ((Lp K 2 μ) × H),
      ‖(L.map (fun xy ↦
          InnerProductSpace.rankOne K xy.1 xy.2)).sum -
        l2SectionOperator (K := K) μ g‖ < ε := by
  obtain ⟨q₀, hq⟩ :=
    (Lp.simpleFunc.denseRange (E := H) (p := (2 : ℝ≥0∞)) (μ := μ)
      ENNReal.ofNat_ne_top).exists_dist_lt g hε
  rcases exists_list_l2SectionOperator_eq_sum_rankOne
    (K := K) μ q₀ with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  rw [← hL]
  refine (norm_l2SectionOperator_sub_le (K := K) μ
    (q₀ : Lp H 2 μ) g).trans_lt ?_
  simpa only [dist_eq_norm, norm_sub_rev] using hq

/-- Every square-integrable Hilbert-valued section induces a compact
operator.  The proof combines `Lp.simpleFunc.induction` with simple-function
density: indicator sections are rank one, their finite sums approximate the
section operator in norm, and compact operators are operator-norm closed. -/
theorem isCompactOperator_l2SectionOperator (μ : Measure α)
    (g : Lp H 2 μ) :
    IsCompactOperator (l2SectionOperator (K := K) μ g) := by
  apply isCompactOperator_of_list_rankOne_approximation (K := K)
  intro ε hε
  exact exists_list_rankOne_approx_l2SectionOperator (K := K) μ g ε hε

end

end FastDynamo

/-!
## Compactness of the whole-plane band-limited restriction

This part realizes the space--frequency truncated inverse Fourier transform
as an operator associated with an `L²` family of Hilbert-space sections.  The
abstract compactness theorem proved above then gives the coefficient-level
compactness input for local Rellich.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform ComplexConjugate

/-! ## Frequency kernel sections -/

/-- The conjugated frequency kernel representing inverse Fourier evaluation
as the `L²` inner product `⟪g x, c⟫`. -/
def wholePlaneBandLimitedKernelFn
    (R : ℝ) (x xi : WholePlane) : ℂ :=
  conj ((Real.fourierChar (inner ℝ xi x) : ℂ) *
    h1LowFrequencyRecoverMass R xi)

/-- For fixed space variable `x`, the frequency kernel is strongly measurable in `ξ`, being
the product of a continuous character with the strongly measurable low-frequency symbol. -/
theorem wholePlaneBandLimitedKernelFn_stronglyMeasurable
    (R : ℝ) (x : WholePlane) :
    StronglyMeasurable (wholePlaneBandLimitedKernelFn R x) := by
  unfold wholePlaneBandLimitedKernelFn
  have hinner : Continuous (fun xi : WholePlane ↦ inner ℝ xi x) := by
    fun_prop
  have hchar : StronglyMeasurable (fun xi : WholePlane ↦
      (Real.fourierChar (inner ℝ xi x) : ℂ)) :=
    ((Real.continuous_fourierChar.comp hinner).subtype_val).stronglyMeasurable
  exact Complex.continuous_conj.comp_stronglyMeasurable
    (hchar.mul (h1LowFrequencyRecoverMass_stronglyMeasurable R))

/-- The frequency kernel is bounded by one everywhere, the character having unit modulus
and the low-frequency symbol being contractive. -/
theorem norm_wholePlaneBandLimitedKernelFn_le_one
    (R : ℝ) (x xi : WholePlane) :
    ‖wholePlaneBandLimitedKernelFn R x xi‖ ≤ 1 := by
  rw [wholePlaneBandLimitedKernelFn, Complex.norm_conj, norm_mul,
    Circle.norm_coe, one_mul]
  exact norm_h1LowFrequencyRecoverMass_le_one R xi

/-- The frequency kernel vanishes at every frequency with `R ≤ ‖ξ‖`, hence is supported in
the frequency ball of radius `R`. -/
theorem wholePlaneBandLimitedKernelFn_eq_zero_of_norm_ge
    (R : ℝ) (x xi : WholePlane) (hxi : R ≤ ‖xi‖) :
    wholePlaneBandLimitedKernelFn R x xi = 0 := by
  simp [wholePlaneBandLimitedKernelFn, h1LowFrequencyRecoverMass, hxi]

/-- Being bounded and supported in a ball of finite measure, the frequency kernel is square
integrable in `ξ` for each fixed `x`. -/
theorem wholePlaneBandLimitedKernelFn_memLp_two
    (R : ℝ) (x : WholePlane) :
    MemLp (wholePlaneBandLimitedKernelFn R x) 2 volume := by
  have hbound := memLp_top_of_bound (μ := (volume : Measure WholePlane))
    (wholePlaneBandLimitedKernelFn_stronglyMeasurable R x).aestronglyMeasurable
    1 (ae_of_all _ (norm_wholePlaneBandLimitedKernelFn_le_one R x))
  exact hbound.mono_exponent_of_measure_support_ne_top
      (s := Metric.ball (0 : WholePlane) R)
      (fun xi hxi ↦
        wholePlaneBandLimitedKernelFn_eq_zero_of_norm_ge R x xi (by
          simpa [Metric.mem_ball, dist_zero_right, not_lt] using hxi))
      measure_ball_lt_top.ne (by norm_num)

/-- A frequency kernel section as an element of scalar `L²(ℝ²)`. -/
def wholePlaneBandLimitedKernelSection
    (R : ℝ) (x : WholePlane) : WholePlaneScalarL2 :=
  (wholePlaneBandLimitedKernelFn_memLp_two R x).toLp _

/-- The `L²` section at `x` has the pointwise frequency kernel `wholePlaneBandLimitedKernelFn R x`
as an almost everywhere representative. -/
theorem wholePlaneBandLimitedKernelSection_coe_ae
    (R : ℝ) (x : WholePlane) :
    (wholePlaneBandLimitedKernelSection R x : WholePlane → ℂ) =ᵐ[volume]
      wholePlaneBandLimitedKernelFn R x := by
  exact MemLp.coeFn_toLp _

/-- The scalar `L²` indicator of the frequency ball supporting the kernel. -/
def wholePlaneBandLimitedFrequencyIndicator (R : ℝ) :
    WholePlaneScalarL2 :=
  indicatorConstLp 2 (measurableSet_ball :
      MeasurableSet (Metric.ball (0 : WholePlane) R))
    measure_ball_lt_top.ne (1 : ℂ)

/-- The `L²` class of the frequency-ball indicator has the set indicator of
`Metric.ball 0 R` as an almost everywhere representative. -/
theorem wholePlaneBandLimitedFrequencyIndicator_coe_ae (R : ℝ) :
    (wholePlaneBandLimitedFrequencyIndicator R : WholePlane → ℂ) =ᵐ[volume]
      (Metric.ball (0 : WholePlane) R).indicator (fun _ ↦ (1 : ℂ)) := by
  exact indicatorConstLp_coeFn

/-- Uniform frequency-space bound for every spatial kernel section. -/
theorem norm_wholePlaneBandLimitedKernelSection_le
    (R : ℝ) (x : WholePlane) :
    ‖wholePlaneBandLimitedKernelSection R x‖ ≤
      ‖wholePlaneBandLimitedFrequencyIndicator R‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [
    wholePlaneBandLimitedKernelSection_coe_ae R x,
    wholePlaneBandLimitedFrequencyIndicator_coe_ae R]
    with xi hkernel hindicator
  rw [hkernel, hindicator]
  by_cases hxi : xi ∈ Metric.ball (0 : WholePlane) R
  · rw [Set.indicator_of_mem hxi]
    simpa using norm_wholePlaneBandLimitedKernelFn_le_one R x xi
  · rw [Set.indicator_of_notMem hxi,
      wholePlaneBandLimitedKernelFn_eq_zero_of_norm_ge R x xi (by
        simpa [Metric.mem_ball, dist_zero_right, not_lt] using hxi)]

/-! ## Dependence on the spatial parameter -/

/-- The analyst-normalized real Fourier character is globally Lipschitz,
with the harmless constant `2π`. -/
theorem norm_fourierChar_sub_le (a b : ℝ) :
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖ ≤
      2 * Real.pi * |a - b| := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply]
  let A : ℂ := ↑(2 * Real.pi * a) * Complex.I
  let B : ℂ := ↑(2 * Real.pi * b) * Complex.I
  have hfactor : Complex.exp A - Complex.exp B =
      Complex.exp B * (Complex.exp (A - B) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  change ‖Complex.exp A - Complex.exp B‖ ≤ _
  rw [hfactor, norm_mul, Complex.norm_exp]
  have hBre : B.re = 0 := by simp [B]
  rw [hBre, Real.exp_zero, one_mul]
  calc
    ‖Complex.exp (A - B) - 1‖ =
        ‖Complex.exp (Complex.I * (2 * Real.pi * (a - b))) - 1‖ := by
      congr 3
      simp [A, B]
      ring
    _ ≤ ‖2 * Real.pi * (a - b)‖ := by
      simpa using (Real.norm_exp_I_mul_ofReal_sub_one_le
        (x := 2 * Real.pi * (a - b)))
    _ = 2 * Real.pi * |a - b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
        abs_of_nonneg Real.pi_pos.le]

/-- A coarse global Lipschitz bound for the frequency kernel.  Compact
frequency support turns the factor `‖xi‖` into the finite constant
`|R| + 1`. -/
theorem norm_wholePlaneBandLimitedKernelFn_sub_le
    (R : ℝ) (x y xi : WholePlane) :
    ‖wholePlaneBandLimitedKernelFn R x xi -
        wholePlaneBandLimitedKernelFn R y xi‖ ≤
      2 * Real.pi * (|R| + 1) * ‖x - y‖ := by
  by_cases hxi : R ≤ ‖xi‖
  · rw [wholePlaneBandLimitedKernelFn_eq_zero_of_norm_ge R x xi hxi,
      wholePlaneBandLimitedKernelFn_eq_zero_of_norm_ge R y xi hxi,
      sub_self, norm_zero]
    positivity
  · have hxiR : ‖xi‖ < R := lt_of_not_ge hxi
    have hxiAbs : ‖xi‖ ≤ |R| + 1 := by
      have hRabs : R ≤ |R| := le_abs_self R
      linarith
    rw [wholePlaneBandLimitedKernelFn, wholePlaneBandLimitedKernelFn,
      ← map_sub, Complex.norm_conj, ← sub_mul, norm_mul]
    have hchar := norm_fourierChar_sub_le
      (inner ℝ xi x) (inner ℝ xi y)
    have hinner : |inner ℝ xi x - inner ℝ xi y| ≤
        ‖xi‖ * ‖x - y‖ := by
      rw [← inner_sub_right]
      exact abs_real_inner_le_norm xi (x - y)
    calc
      ‖(Real.fourierChar (inner ℝ xi x) : ℂ) -
          (Real.fourierChar (inner ℝ xi y) : ℂ)‖ *
          ‖h1LowFrequencyRecoverMass R xi‖ ≤
          2 * Real.pi * |inner ℝ xi x - inner ℝ xi y| := by
        simpa using mul_le_mul hchar
          (norm_h1LowFrequencyRecoverMass_le_one R xi)
          (norm_nonneg _) (by positivity : 0 ≤ 2 * Real.pi *
            |inner ℝ xi x - inner ℝ xi y|)
      _ ≤ 2 * Real.pi * (‖xi‖ * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ ≤ 2 * Real.pi * ((|R| + 1) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hxiAbs (norm_nonneg _))
          (by positivity)
      _ = 2 * Real.pi * (|R| + 1) * ‖x - y‖ := by ring

/-- The pointwise kernel estimate integrated in frequency. -/
theorem norm_wholePlaneBandLimitedKernelSection_sub_le
    (R : ℝ) (x y : WholePlane) :
    ‖wholePlaneBandLimitedKernelSection R x -
        wholePlaneBandLimitedKernelSection R y‖ ≤
      (2 * Real.pi * (|R| + 1) * ‖x - y‖) *
        ‖wholePlaneBandLimitedFrequencyIndicator R‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    Lp.coeFn_sub (wholePlaneBandLimitedKernelSection R x)
      (wholePlaneBandLimitedKernelSection R y),
    wholePlaneBandLimitedKernelSection_coe_ae R x,
    wholePlaneBandLimitedKernelSection_coe_ae R y,
    wholePlaneBandLimitedFrequencyIndicator_coe_ae R]
    with xi hsub hx hy hindicator
  rw [hsub, Pi.sub_apply, hx, hy, hindicator]
  by_cases hxi : xi ∈ Metric.ball (0 : WholePlane) R
  · rw [Set.indicator_of_mem hxi, norm_one, mul_one]
    exact norm_wholePlaneBandLimitedKernelFn_sub_le R x y xi
  · rw [Set.indicator_of_notMem hxi, norm_zero, mul_zero,
      wholePlaneBandLimitedKernelFn_eq_zero_of_norm_ge R x xi (by
        simpa [Metric.mem_ball, dist_zero_right, not_lt] using hxi),
      wholePlaneBandLimitedKernelFn_eq_zero_of_norm_ge R y xi (by
        simpa [Metric.mem_ball, dist_zero_right, not_lt] using hxi),
      sub_self, norm_zero]

/-- An explicit nonnegative Lipschitz constant for the spatially parameterized
frequency section. -/
def wholePlaneBandLimitedKernelLipschitzConstant (R : ℝ) : NNReal :=
  ⟨2 * Real.pi * (|R| + 1) *
      ‖wholePlaneBandLimitedFrequencyIndicator R‖,
    by positivity⟩

/-- The map sending a space point `x` to its frequency section is Lipschitz into
`L²(ℝ²)`, with the explicit constant `2π (|R| + 1) ‖1_{B_R}‖`; this equicontinuity in the
space variable is the Arzelà–Ascoli input for compactness. -/
theorem lipschitzWith_wholePlaneBandLimitedKernelSection (R : ℝ) :
    LipschitzWith (wholePlaneBandLimitedKernelLipschitzConstant R)
      (wholePlaneBandLimitedKernelSection R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  calc
    ‖wholePlaneBandLimitedKernelSection R x -
        wholePlaneBandLimitedKernelSection R y‖ ≤
        (2 * Real.pi * (|R| + 1) * ‖x - y‖) *
          ‖wholePlaneBandLimitedFrequencyIndicator R‖ :=
      norm_wholePlaneBandLimitedKernelSection_sub_le R x y
    _ = (wholePlaneBandLimitedKernelLipschitzConstant R : ℝ) *
        ‖x - y‖ := by
      change (2 * Real.pi * (|R| + 1) * ‖x - y‖) *
          ‖wholePlaneBandLimitedFrequencyIndicator R‖ =
        (2 * Real.pi * (|R| + 1) *
          ‖wholePlaneBandLimitedFrequencyIndicator R‖) * ‖x - y‖
      ring

/-- The frequency section depends continuously on the space point, being Lipschitz. -/
theorem continuous_wholePlaneBandLimitedKernelSection (R : ℝ) :
    Continuous (wholePlaneBandLimitedKernelSection R) :=
  (lipschitzWith_wholePlaneBandLimitedKernelSection R).continuous

/-- The frequency section is a strongly measurable Hilbert-space valued function of the
space point. -/
theorem stronglyMeasurable_wholePlaneBandLimitedKernelSection (R : ℝ) :
    StronglyMeasurable (wholePlaneBandLimitedKernelSection R) :=
  (continuous_wholePlaneBandLimitedKernelSection R).stronglyMeasurable

/-! ## Spatially truncated Hilbert-valued section -/

/-- The frequency kernel section, set to zero outside the spatial cutoff. -/
def wholePlaneBandLimitedSpatialKernelSectionFn
    (s : Set WholePlane) (R : ℝ) (x : WholePlane) :
    WholePlaneScalarL2 :=
  s.indicator (wholePlaneBandLimitedKernelSection R) x

/-- Truncating the section to a measurable spatial set preserves strong measurability. -/
theorem wholePlaneBandLimitedSpatialKernelSectionFn_stronglyMeasurable
    (s : Set WholePlane) (hs : MeasurableSet s) (R : ℝ) :
    StronglyMeasurable
      (wholePlaneBandLimitedSpatialKernelSectionFn s R) := by
  exact (stronglyMeasurable_wholePlaneBandLimitedKernelSection R).indicator hs

/-- The spatially truncated section is bounded, uniformly in `x`, by the `L²` norm of the
frequency-ball indicator. -/
theorem norm_wholePlaneBandLimitedSpatialKernelSectionFn_le
    (s : Set WholePlane) (R : ℝ) (x : WholePlane) :
    ‖wholePlaneBandLimitedSpatialKernelSectionFn s R x‖ ≤
      ‖wholePlaneBandLimitedFrequencyIndicator R‖ := by
  by_cases hx : x ∈ s
  · simpa [wholePlaneBandLimitedSpatialKernelSectionFn,
      Set.indicator_of_mem hx] using
        norm_wholePlaneBandLimitedKernelSection_le R x
  · simp [wholePlaneBandLimitedSpatialKernelSectionFn,
      Set.indicator_of_notMem hx]

/-- On a measurable spatial set of finite measure the truncated section is a square
integrable Hilbert-space valued function, which is exactly the Hilbert–Schmidt condition
used by the abstract section-operator compactness theorem. -/
theorem wholePlaneBandLimitedSpatialKernelSectionFn_memLp_two
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) (R : ℝ) :
    MemLp (wholePlaneBandLimitedSpatialKernelSectionFn s R) 2 volume := by
  have hbound := memLp_top_of_bound (μ := (volume : Measure WholePlane))
      (wholePlaneBandLimitedSpatialKernelSectionFn_stronglyMeasurable
        s hs R).aestronglyMeasurable
      ‖wholePlaneBandLimitedFrequencyIndicator R‖
      (ae_of_all _ (norm_wholePlaneBandLimitedSpatialKernelSectionFn_le s R))
  exact hbound.mono_exponent_of_measure_support_ne_top
      (s := s)
      (fun x hx ↦ by
        simp [wholePlaneBandLimitedSpatialKernelSectionFn,
          Set.indicator_of_notMem hx])
      hsm (by norm_num)

/-- The square-integrable Hilbert-valued section which generates the
space--frequency truncated operator. -/
def wholePlaneBandLimitedKernelL2Section
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) (R : ℝ) :
    Lp WholePlaneScalarL2 2 (volume : Measure WholePlane) :=
  (wholePlaneBandLimitedSpatialKernelSectionFn_memLp_two
    s hs hsm R).toLp _

/-- The bundled `L²` section has the spatially truncated pointwise section as an almost
everywhere representative. -/
theorem wholePlaneBandLimitedKernelL2Section_coe_ae
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) (R : ℝ) :
    (wholePlaneBandLimitedKernelL2Section s hs hsm R :
        WholePlane → WholePlaneScalarL2) =ᵐ[volume]
      wholePlaneBandLimitedSpatialKernelSectionFn s R := by
  exact MemLp.coeFn_toLp _

/-! ## Inner-product identification -/

/-- Pairing a coefficient against the kernel section at `x` reproduces the band-limited
inverse Fourier integral `∫ e(⟪ξ, x⟫) m_R(ξ) c(ξ) dξ` evaluated at `x`. -/
theorem inner_wholePlaneBandLimitedKernelSection
    (R : ℝ) (x : WholePlane) (c : WholePlaneScalarL2) :
    inner ℂ (wholePlaneBandLimitedKernelSection R x) c =
      ∫ xi : WholePlane,
        (Real.fourierChar (inner ℝ xi x) : ℂ) *
          h1LowFrequencyRecoverMass R xi * c xi := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [wholePlaneBandLimitedKernelSection_coe_ae R x]
    with xi hkernel
  rw [hkernel]
  simp [wholePlaneBandLimitedKernelFn, mul_assoc]
  ring

/-! ## Operator identity and compactness -/

/-- The abstract section operator is exactly the spatially restricted
band-limited synthesis. -/
theorem l2SectionOperator_wholePlaneBandLimitedKernelL2Section
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) (R : ℝ) :
    l2SectionOperator (K := ℂ) volume
        (wholePlaneBandLimitedKernelL2Section s hs hsm R) =
      wholePlaneBandLimitedRestrictionFromCoeff s hs hsm R := by
  apply ContinuousLinearMap.ext
  intro c
  apply Lp.ext
  have hleft := l2SectionOperator_apply_coe_ae (K := ℂ) volume
    (wholePlaneBandLimitedKernelL2Section s hs hsm R) c
  have hsection := wholePlaneBandLimitedKernelL2Section_coe_ae
    s hs hsm R
  have hcutoff := scalarVectorMulL2_coe_ae (E := ℂ) volume
    (wholePlaneLocalizationIndicator s hs hsm)
    (wholePlaneH1LowFrequencyFromCoeff ℂ R c)
  have hindicator := indicatorConstLp_coeFn
    (p := ∞) (hs := hs) (hμs := hsm) (c := (1 : ℂ))
  change (wholePlaneLocalizationIndicator s hs hsm : WholePlane → ℂ) =ᵐ[volume]
    s.indicator (fun _ ↦ (1 : ℂ)) at hindicator
  have hintegral :=
    wholePlaneH1LowFrequencyFromCoeff_ae_eq_integral R c
  filter_upwards [hleft, hsection, hcutoff, hindicator, hintegral]
    with x hleftx hsectionx hcutoffx hindicatorx hintegralx
  change
    (l2SectionOperator (K := ℂ) volume
        (wholePlaneBandLimitedKernelL2Section s hs hsm R) c :
      WholePlane → ℂ) x =
    (scalarVectorMulL2 (E := ℂ) volume
        (wholePlaneLocalizationIndicator s hs hsm)
        (wholePlaneH1LowFrequencyFromCoeff ℂ R c) :
      WholePlane → ℂ) x
  rw [hleftx, hsectionx, hcutoffx, hindicatorx, hintegralx]
  change inner ℂ
      (wholePlaneBandLimitedSpatialKernelSectionFn s R x) c =
    (s.indicator (fun _ ↦ (1 : ℂ)) x) •
      ∫ xi : WholePlane,
        (Real.fourierChar (inner ℝ xi x) : ℂ) *
          h1LowFrequencyRecoverMass R xi * c xi
  by_cases hx : x ∈ s
  · rw [wholePlaneBandLimitedSpatialKernelSectionFn,
      Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      inner_wholePlaneBandLimitedKernelSection]
    simp
  · rw [wholePlaneBandLimitedSpatialKernelSectionFn,
      Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- The coefficient-level space--frequency concentration operator is compact
for every finite-measure spatial cutoff and every real frequency radius. -/
theorem isCompactOperator_wholePlaneBandLimitedRestrictionFromCoeff
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) (R : ℝ) :
    IsCompactOperator
      (wholePlaneBandLimitedRestrictionFromCoeff s hs hsm R) := by
  rw [← l2SectionOperator_wholePlaneBandLimitedKernelL2Section
    s hs hsm R]
  exact isCompactOperator_l2SectionOperator (K := ℂ) volume
    (wholePlaneBandLimitedKernelL2Section s hs hsm R)

end

end FastDynamo

/-!
## Scalar local Rellich on the whole plane

The concrete kernel theorem supplies every band-limited compactness premise
required by `WholePlaneBandLimitedRellich`.  This part records the resulting
finite-measure specialization without importing any local Ponomarenko
coefficient module.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- Restriction from scalar whole-plane `H¹` to any measurable set of finite
volume is compact. -/
theorem isCompactOperator_wholePlaneScalarRestrictionH1
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) :
    IsCompactOperator (wholePlaneScalarRestrictionH1 s hs hsm) := by
  exact
    isCompactOperator_wholePlaneScalarRestrictionH1_of_bandLimited_cores
      s hs hsm (fun n ↦
        isCompactOperator_wholePlaneBandLimitedRestrictionFromCoeff
          s hs hsm ((n : ℝ) + 1))

end

end FastDynamo

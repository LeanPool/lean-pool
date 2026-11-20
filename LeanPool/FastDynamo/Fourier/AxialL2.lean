/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.FastDynamo.Conventions
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Axial Fourier modes and the axial lift on `L²`

The construction of Sections 5 and 8 lifts a transverse amplitude
`b : T² → C³` to the `x₃`-Fourier mode `V(y, x₃) = e^{2π i K x₃} b(y)`, and then
passes to its real part.  This module builds that lift, first pointwise and then
on `L²` of the product torus, and proves the paper's Lemma 8.2
(`lem:real-axial-mode`, equation `eq:real-part-norm`): for `K ≠ 0` and every
real phase `φ`,

`∫₀¹ |re (e^{i φ} e^{2π i K x₃} b(y))|² dx₃ = ½ |b(y)|²`.

The nonzero axial index removes the oscillatory cross term, so no temporal phase
can make the real part of a nonzero mode vanish or change its norm.  This is
what makes the real datum `B_in = re V` nonzero and supplies the exact norm law
used in the proof of Theorem 1.2.

Everything stays at quotient level: characters live intrinsically on `ℝ / ℤ`,
the transverse, axial and product measures are all normalized, and the complex
lift is an isometry `TransverseC3L2 →ₗᵢ[ℂ] ProductC3L2`.  The real-part map, by
contrast, is only real-linear, with codomain the real `L²` space.

## Contents

* **Axial Fourier modes.** `axialCharacter` with its group law, unit modulus and
  derivative, the multiplier `axialMultiplier`, and the pointwise lift
  `axialLiftPointwise`; then the scalar core of Lemma 8.2 and its
  vector-valued form `vecRe` and `realPart_axialLiftPointwise_norm_sq`.
* **The axial lift on `L²`.** The normalized measures and the spaces
  `TransverseC3L2`, `ProductC3L2`, `ProductR3L2`; the isometric complex lift
  `axialLiftL2`; the coordinatewise real part `realPartL2`; and the global
  real-phase identity `phaseAxialFieldL2_norm_sq` together with its corollaries
  `phaseAxialFieldL2_ne_zero` and `phaseAxialFieldL2_norm_sq_eq`.
-/

@[expose] public section

/-!
## Axial Fourier modes

The pointwise part of the axial-mode calculus of Sections 5 and 8.  Characters are defined
intrinsically on `ℝ / ℤ`; no representative of a circle point is chosen.  The
derivative statements are made on the canonical real lift.
-/

namespace FastDynamo

noncomputable section

/-- The normalized axial character `x₃ ↦ exp (2π i K x₃)`. -/
def axialCharacter (K : ℤ) : C(AxialCircle, ℂ) :=
  fourier K

/--
The axial character evaluates to Mathlib's unit-period character `fourier K`; `axialCharacter`
is definitionally that continuous map.
-/
@[simp] theorem axialCharacter_apply (K : ℤ) (x : AxialCircle) :
    axialCharacter K x = fourier K x :=
  rfl

/--
The axial character takes values in the unit circle, so lifting a transverse amplitude by it is
an isometry pointwise.
-/
theorem norm_axialCharacter (K : ℤ) (x : AxialCircle) :
    ‖axialCharacter K x‖ = 1 := by
  simp [axialCharacter, fourier_apply, Circle.norm_coe]

/--
Negating the axial index conjugates the character; combined with unit modulus this gives the
inverse character.
-/
theorem axialCharacter_neg (K : ℤ) (x : AxialCircle) :
    axialCharacter (-K) x = star (axialCharacter K x) := by
  exact fourier_neg

/-- The complex multiplier representing one axial derivative. -/
def axialMultiplier (K : ℤ) : ℂ :=
  2 * Real.pi * Complex.I * K

/-- Pointwise lift of a transverse amplitude into one axial Fourier sector. -/
def axialLiftPointwise (K : ℤ) (b : AxialAmplitudeRaw) : ProductTorus3 → C3 :=
  fun x => axialCharacter K x.2 • b x.1

/--
The pointwise axial lift evaluates at `(y, x₃)` to the character `axialCharacter K x₃` times the
transverse amplitude `b y`.
-/
@[simp] theorem axialLiftPointwise_apply (K : ℤ) (b : AxialAmplitudeRaw)
    (y : TransverseTorus) (x₃ : AxialCircle) :
    axialLiftPointwise K b (y, x₃) = axialCharacter K x₃ • b y :=
  rfl

/-! ## The scalar core of Lemma 8.2 -/

open MeasureTheory

/-- Every nonconstant unit-circle Fourier character has Haar mean zero. -/
lemma integral_fourier_eq_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x : AxialCircle, fourier n x ∂AddCircle.haarAddCircle = 0 := by
  have h := (orthonormal_iff_ite.mp
    (orthonormal_fourier (T := (1 : ℝ)))) 0 n
  simpa [MeasureTheory.ContinuousMap.inner_toLp, Ne.symm hn] using h

/-- Algebraic decomposition that isolates the doubled Fourier frequency. -/
lemma re_sq_identity (w : ℂ) :
    w.re ^ 2 = (1 / 2 : ℝ) * (‖w‖ ^ 2 + (w ^ 2).re) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re]
  ring

/--
Scalar Haar-integral form of the phase-independent half-norm identity.  The
unit complex number `η` includes the arbitrary phase from Lemma 8.2.
-/
lemma integral_sq_re_mul_fourier (K : ℤ) (hK : K ≠ 0)
    (η z : ℂ) (hη : ‖η‖ = 1) :
    ∫ x : AxialCircle, ((η * fourier K x * z).re) ^ 2
        ∂AddCircle.haarAddCircle = (1 / 2 : ℝ) * ‖z‖ ^ 2 := by
  have h2K : K + K ≠ 0 := by omega
  have hsquare_integrable :
      Integrable (fun x : AxialCircle => (η * fourier K x * z) ^ 2)
        AddCircle.haarAddCircle := by
    have hc : Continuous (fun x : AxialCircle =>
        (η * fourier K x * z) ^ 2) := by fun_prop
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsquare :
      ∫ x : AxialCircle, (η * fourier K x * z) ^ 2
          ∂AddCircle.haarAddCircle = 0 := by
    calc
      _ = ∫ x : AxialCircle, (η ^ 2 * z ^ 2) * fourier (K + K) x
            ∂AddCircle.haarAddCircle := by
          apply integral_congr_ae
          filter_upwards with x
          rw [fourier_add]
          ring
      _ = (η ^ 2 * z ^ 2) *
            ∫ x : AxialCircle, fourier (K + K) x
              ∂AddCircle.haarAddCircle := by rw [integral_const_mul]
      _ = 0 := by rw [integral_fourier_eq_zero h2K, mul_zero]
  have hreal_integrable :
      Integrable (fun x : AxialCircle =>
        ((η * fourier K x * z) ^ 2).re) AddCircle.haarAddCircle := by
    simpa only [RCLike.re_eq_complex_re] using hsquare_integrable.re
  have hreal :
      ∫ x : AxialCircle, ((η * fourier K x * z) ^ 2).re
          ∂AddCircle.haarAddCircle = 0 := by
    have hr := integral_re hsquare_integrable
    rw [RCLike.re_eq_complex_re] at hr
    rw [hr, hsquare]
    rfl
  calc
    _ = ∫ x : AxialCircle,
          (1 / 2 : ℝ) * (‖z‖ ^ 2 + ((η * fourier K x * z) ^ 2).re)
          ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards with x
        rw [re_sq_identity]
        congr 2
        simp [hη, fourier_apply, Circle.norm_coe]
    _ = (1 / 2 : ℝ) * ∫ x : AxialCircle,
          (‖z‖ ^ 2 + ((η * fourier K x * z) ^ 2).re)
          ∂AddCircle.haarAddCircle := by rw [integral_const_mul]
    _ = (1 / 2 : ℝ) * ‖z‖ ^ 2 := by
      rw [integral_add (integrable_const _) hreal_integrable,
        integral_const, hreal]
      simp

/-! ## Vector-valued form of Lemma 8.2 -/

/-- Coordinatewise real part from a complex Euclidean space to its real form. -/
def vecRe {ι : Type*} (z : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => (z i).re

/--
The coordinatewise real part `vecRe` has `i`-th coordinate the real part of the `i`-th
coordinate of `z`.
-/
@[simp] lemma vecRe_apply {ι : Type*} (z : EuclideanSpace ℂ ι) (i : ι) :
    vecRe z i = (z i).re :=
  rfl

/-- Componentwise extension of the scalar half-norm identity. -/
lemma integral_norm_sq_vecRe_smul_fourier {ι : Type*} [Fintype ι]
    (K : ℤ) (hK : K ≠ 0) (η : ℂ) (hη : ‖η‖ = 1)
    (z : EuclideanSpace ℂ ι) :
    ∫ x : AxialCircle, ‖vecRe ((η * fourier K x) • z)‖ ^ 2
      ∂AddCircle.haarAddCircle = (1 / 2 : ℝ) * ‖z‖ ^ 2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, vecRe_apply,
    WithLp.ofLp_smul, Pi.smul_apply]
  rw [integral_finsetSum]
  · simp_rw [smul_eq_mul, integral_sq_re_mul_fourier K hK η _ hη]
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  · intro i hi
    have hc : Continuous (fun x : AxialCircle =>
        ((η * fourier K x * z i).re) ^ 2) := by fun_prop
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/--
Fiberwise `ℂ³` form of `eq:real-part-norm`: for every transverse point, every
phase has exactly half of the complex mode's squared norm.
-/
theorem realPart_axialLiftPointwise_norm_sq (K : ℤ) (hK : K ≠ 0)
    (phase : ℝ) (b : AxialAmplitudeRaw) (y : TransverseTorus) :
    ∫ x : AxialCircle,
        ‖vecRe
          (Complex.exp ((phase : ℂ) * Complex.I) • axialLiftPointwise K b (y, x))‖ ^ 2
          ∂AddCircle.haarAddCircle = (1 / 2 : ℝ) * ‖b y‖ ^ 2 := by
  simpa [axialLiftPointwise, axialCharacter, smul_smul] using
    integral_norm_sq_vecRe_smul_fourier K hK
      (Complex.exp ((phase : ℂ) * Complex.I))
      (Complex.norm_exp_ofReal_mul_I phase) (b y)

/-- Exact norm of the Fourier multiplier representing one axial derivative. -/
theorem norm_axialMultiplier (K : ℤ) :
    ‖axialMultiplier K‖ = 2 * Real.pi * |(K : ℝ)| := by
  simp [axialMultiplier, abs_of_pos Real.pi_pos]

end

end FastDynamo

/-!
## The axial lift on `L²`

The fiber calculation of the previous section is globalized to the product
torus.  The measures are written explicitly: normalized Lebesgue measure on the
transverse unit torus, normalized Haar measure on the axial unit circle, and
their product.

The quotient-level construction has two parts.  Pullback along the transverse
projection is measure preserving, and multiplication by the unit axial
character preserves the norm.  The real-part map is only real-linear; its
codomain is the real `L²` space.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- Normalized measure on the transverse unit two-torus. -/
abbrev transverseMeasure : Measure TransverseTorus := volume

/-- Normalized Haar measure on the axial unit circle. -/
abbrev axialMeasure : Measure AxialCircle := AddCircle.haarAddCircle

/-- Product measure associated with the paper's split `x = (y, x₃)`. -/
abbrev productMeasure : Measure ProductTorus3 :=
  transverseMeasure.prod axialMeasure

/-- Complex transverse amplitudes in `L²`. -/
abbrev TransverseC3L2 := Lp C3 2 transverseMeasure

/-- Complex vector fields on the product model of the three-torus. -/
abbrev ProductC3L2 := Lp C3 2 productMeasure

/-- Real vector fields on the product model of the three-torus. -/
abbrev ProductR3L2 := Lp R3 2 productMeasure

/-! ## The complex axial lift -/

/-- Pullback of a transverse amplitude along the first projection. -/
def pullTransverseL2 : TransverseC3L2 →ₗᵢ[ℂ] ProductC3L2 :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst measurePreserving_fst

/-- The axial character, viewed as a continuous function on the product torus. -/
def productAxialCharacter (K : ℤ) : C(ProductTorus3, ℂ) where
  toFun x := axialCharacter K x.2
  continuous_toFun := by fun_prop

/-- The product axial character as an `L∞` multiplier. -/
def productAxialCharacterLInf (K : ℤ) : Lp ℂ ∞ productMeasure :=
  (productAxialCharacter K).toLp ∞ productMeasure ℂ

/-- Unbundled quotient-level axial lift. -/
def axialLiftL2Fun (K : ℤ) (b : TransverseC3L2) : ProductC3L2 :=
  (productAxialCharacterLInf K • pullTransverseL2 b : ProductC3L2)

/-- The lift is represented almost everywhere by multiplication of the pulled-back amplitude. -/
lemma axialLiftL2Fun_ae_pull (K : ℤ) (b : TransverseC3L2) :
    (axialLiftL2Fun K b : ProductTorus3 → C3) =ᵐ[productMeasure]
      fun x => axialCharacter K x.2 • (pullTransverseL2 b : ProductTorus3 → C3) x := by
  have hmul := Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
    (productAxialCharacterLInf K) (pullTransverseL2 b)
  have hchar := ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ)
    productMeasure (productAxialCharacter K)
  filter_upwards [hmul, hchar] with x hx hχ
  change ((productAxialCharacterLInf K • pullTransverseL2 b : ProductC3L2) :
    ProductTorus3 → C3) x = _
  rw [hx]
  change (productAxialCharacterLInf K : ProductTorus3 → ℂ) x •
    (pullTransverseL2 b : ProductTorus3 → C3) x = _
  change (productAxialCharacterLInf K : ProductTorus3 → ℂ) x =
    axialCharacter K x.2 at hχ
  rw [hχ]

/-- Representative formula for the quotient-level axial lift. -/
theorem axialLiftL2Fun_coe_ae (K : ℤ) (b : TransverseC3L2) :
    (axialLiftL2Fun K b : ProductTorus3 → C3) =ᵐ[productMeasure]
      fun x => axialCharacter K x.2 • b x.1 := by
  have hpull := Lp.coeFn_compMeasurePreserving b
    (measurePreserving_fst (μ := transverseMeasure) (ν := axialMeasure))
  filter_upwards [axialLiftL2Fun_ae_pull K b, hpull] with x hx hb
  change (pullTransverseL2 b : ProductTorus3 → C3) x = b x.1 at hb
  rw [hx, hb]

/-- Multiplication by the axial character preserves the pullback norm. -/
lemma norm_axialLiftL2Fun (K : ℤ) (b : TransverseC3L2) :
    ‖axialLiftL2Fun K b‖ = ‖b‖ := by
  calc
    ‖axialLiftL2Fun K b‖ = ‖pullTransverseL2 b‖ := by
      rw [Lp.norm_def, Lp.norm_def]
      congr 1
      apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      filter_upwards [axialLiftL2Fun_ae_pull K b] with x hx
      rw [hx, norm_smul, norm_axialCharacter, one_mul]
    _ = ‖b‖ := (pullTransverseL2.norm_map b)

/-- The axial Fourier lift as a complex linear isometry. -/
def axialLiftL2 (K : ℤ) : TransverseC3L2 →ₗᵢ[ℂ] ProductC3L2 where
  toFun := axialLiftL2Fun K
  map_add' f g := by
    simp only [axialLiftL2Fun, map_add]
    exact Lp.add_smul (productAxialCharacterLInf K)
      (pullTransverseL2 f) (pullTransverseL2 g)
  map_smul' c f := by
    simp only [axialLiftL2Fun, map_smul]
    simpa only [RingHom.id_apply] using
      (Lp.smul_comm (p := ∞) (q := 2) (r := 2) c
        (productAxialCharacterLInf K) (pullTransverseL2 f)).symm
  norm_map' := norm_axialLiftL2Fun K

/-- Representative formula for the bundled lift. -/
theorem axialLiftL2_coe_ae (K : ℤ) (b : TransverseC3L2) :
    (axialLiftL2 K b : ProductTorus3 → C3) =ᵐ[productMeasure]
      fun x => axialCharacter K x.2 • b x.1 :=
  axialLiftL2Fun_coe_ae K b

/--
The axial Fourier lift is norm-preserving: `‖e^{2π i K x₃} b‖_{L²(T³)} = ‖b‖_{L²(T²)}`, the
norm identity for the eigenmode `V^ε` of Paper Theorem 1.2 (`eq:main-spectral-conclusion`),
which the paper uses without stating it.
-/
theorem norm_axialLiftL2 (K : ℤ) (b : TransverseC3L2) :
    ‖axialLiftL2 K b‖ = ‖b‖ :=
  (axialLiftL2 K).norm_map b

/-! ## Coordinatewise real part on `L²` -/

/-- Coordinatewise real part as a real-linear map. -/
def vecReLinearMap : C3 →ₗ[ℝ] R3 where
  toFun := vecRe
  map_add' z w := by
    ext i
    simp [vecRe]
  map_smul' r z := by
    ext i
    simp [vecRe]

/-- Coordinatewise real part does not increase the Euclidean norm. -/
lemma norm_vecRe_le (z : C3) : ‖vecRe z‖ ≤ ‖z‖ := by
  have hsquare : ‖vecRe z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    change (z i).re ^ 2 ≤ ‖z i‖ ^ 2
    have hre := Complex.abs_re_le_norm (z i)
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg (norm_nonneg (z i))] using hre)
  nlinarith [norm_nonneg (vecRe z), norm_nonneg z]

/-- Coordinatewise real part as a continuous real-linear map. -/
def vecReCLM : C3 →L[ℝ] R3 :=
  LinearMap.mkContinuous vecReLinearMap 1 (by
    intro z
    change ‖vecRe z‖ ≤ 1 * ‖z‖
    simpa using norm_vecRe_le z)

/-- The continuous real-linear map `vecReCLM` acts as the coordinatewise real part `vecRe`. -/
@[simp] theorem vecReCLM_apply (z : C3) : vecReCLM z = vecRe z :=
  rfl

/-- Coordinatewise real part on the product `L²` space. -/
def realPartL2 : ProductC3L2 →L[ℝ] ProductR3L2 :=
  vecReCLM.compLpL 2 productMeasure

/--
A representative of `realPartL2 f` is given almost everywhere by taking the coordinatewise real
part of a representative of `f`.
-/
theorem realPartL2_coe_ae (f : ProductC3L2) :
    (realPartL2 f : ProductTorus3 → R3) =ᵐ[productMeasure]
      fun x => vecRe (f x) := by
  simpa [realPartL2] using vecReCLM.coeFn_compLpL (p := 2) (μ := productMeasure) f

/-! ## The global real-phase identity -/

/-- Raw representative of the real part of a phase-rotated axial mode. -/
def phaseAxialFieldRaw (K : ℤ) (phase : ℝ) (b : TransverseC3L2) :
    ProductTorus3 → R3 :=
  fun x => vecRe
    (Complex.exp ((phase : ℂ) * Complex.I) •
      (axialCharacter K x.2 • b x.1))

/-- Real part of a phase-rotated axial mode as an `L²` class. -/
def phaseAxialFieldL2 (K : ℤ) (phase : ℝ) (b : TransverseC3L2) : ProductR3L2 :=
  realPartL2
    (Complex.exp ((phase : ℂ) * Complex.I) • axialLiftL2 K b)

/-- Representative formula for the phase-rotated real field. -/
theorem phaseAxialFieldL2_coe_ae (K : ℤ) (phase : ℝ) (b : TransverseC3L2) :
    (phaseAxialFieldL2 K phase b : ProductTorus3 → R3) =ᵐ[productMeasure]
      phaseAxialFieldRaw K phase b := by
  have hre := realPartL2_coe_ae
    (Complex.exp ((phase : ℂ) * Complex.I) • axialLiftL2 K b)
  have hphase := Lp.coeFn_smul
    (Complex.exp ((phase : ℂ) * Complex.I)) (axialLiftL2 K b)
  have hlift := axialLiftL2_coe_ae K b
  filter_upwards [hre, hphase, hlift] with x hx hφ hL
  change (realPartL2
    (Complex.exp ((phase : ℂ) * Complex.I) • axialLiftL2 K b) :
      ProductTorus3 → R3) x = phaseAxialFieldRaw K phase b x
  rw [hx, hφ]
  simp only [Pi.smul_apply]
  rw [hL]
  rfl

/-- For an `L²` class, the integral of the pointwise squared norm is its squared norm. -/
lemma integral_norm_sq_coe_eq_norm_sq
    {α E 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (f : Lp E 2 μ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  have h := congrArg (fun z : 𝕜 => RCLike.re z) (L2.inner_def f f)
  rw [← integral_re (L2.integrable_inner (𝕜 := 𝕜) f f)] at h
  simpa only [← norm_sq_eq_re_inner] using h.symm

/--
Global quotient-level form of Lemma 8.2.  It is the identity used in the proof of
`thm:main` to prevent cancellation at a temporal phase.
-/
theorem phaseAxialFieldL2_norm_sq (K : ℤ) (hK : K ≠ 0)
    (phase : ℝ) (b : TransverseC3L2) :
    ‖phaseAxialFieldL2 K phase b‖ ^ 2 =
      (1 / 2 : ℝ) * ‖b‖ ^ 2 := by
  let u : ProductR3L2 := phaseAxialFieldL2 K phase b
  let raw : ProductTorus3 → R3 := phaseAxialFieldRaw K phase b
  have hueq : (u : ProductTorus3 → R3) =ᵐ[productMeasure] raw := by
    simpa [u, raw] using phaseAxialFieldL2_coe_ae K phase b
  have hu_integrable : Integrable (fun x => ‖u x‖ ^ 2) productMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hnormeq : (fun x => ‖u x‖ ^ 2) =ᵐ[productMeasure]
      fun x => ‖raw x‖ ^ 2 := by
    filter_upwards [hueq] with x hx
    rw [hx]
  have hraw_integrable : Integrable (fun x => ‖raw x‖ ^ 2) productMeasure :=
    hu_integrable.congr hnormeq
  calc
    ‖phaseAxialFieldL2 K phase b‖ ^ 2 =
        ∫ x : ProductTorus3, ‖u x‖ ^ 2 ∂productMeasure := by
      simpa [u] using
        (integral_norm_sq_coe_eq_norm_sq (𝕜 := ℝ) u).symm
    _ = ∫ x : ProductTorus3, ‖raw x‖ ^ 2 ∂productMeasure :=
      integral_congr_ae hnormeq
    _ = ∫ y : TransverseTorus,
          ∫ x : AxialCircle, ‖raw (y, x)‖ ^ 2 ∂axialMeasure
        ∂transverseMeasure := by
      exact integral_prod (fun x : ProductTorus3 => ‖raw x‖ ^ 2) hraw_integrable
    _ = ∫ y : TransverseTorus, (1 / 2 : ℝ) * ‖b y‖ ^ 2
        ∂transverseMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      simpa [raw, phaseAxialFieldRaw, axialLiftPointwise, axialMeasure,
        smul_smul] using
        realPart_axialLiftPointwise_norm_sq K hK phase
          (fun y : TransverseTorus => b y) y
    _ = (1 / 2 : ℝ) *
        ∫ y : TransverseTorus, ‖b y‖ ^ 2 ∂transverseMeasure := by
      rw [integral_const_mul]
    _ = (1 / 2 : ℝ) * ‖b‖ ^ 2 := by
      rw [integral_norm_sq_coe_eq_norm_sq (𝕜 := ℂ)]

/-- No phase can make the real part of a nonzero axial `L²` mode vanish. -/
theorem phaseAxialFieldL2_ne_zero (K : ℤ) (hK : K ≠ 0)
    (phase : ℝ) {b : TransverseC3L2} (hb : b ≠ 0) :
    phaseAxialFieldL2 K phase b ≠ 0 := by
  intro hzero
  have hnorm := phaseAxialFieldL2_norm_sq K hK phase b
  rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
  have hb_norm : ‖b‖ = 0 := by
    nlinarith [norm_nonneg b]
  exact hb (norm_eq_zero.mp hb_norm)

/-- The squared norm is independent of the chosen real phase. -/
theorem phaseAxialFieldL2_norm_sq_eq (K : ℤ) (hK : K ≠ 0)
    (phase₁ phase₂ : ℝ) (b : TransverseC3L2) :
    ‖phaseAxialFieldL2 K phase₁ b‖ ^ 2 =
      ‖phaseAxialFieldL2 K phase₂ b‖ ^ 2 := by
  rw [phaseAxialFieldL2_norm_sq K hK phase₁ b,
    phaseAxialFieldL2_norm_sq K hK phase₂ b]

end

end FastDynamo

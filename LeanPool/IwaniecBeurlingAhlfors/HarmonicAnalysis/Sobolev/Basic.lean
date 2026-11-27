/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Weak derivatives and local Sobolev spaces

For a real normed space `E` with a measure (`volume`), an open set `Ω ⊆ E` and functions with
values in a real normed space `F`:

* `HarmonicAnalysis.MemLpLoc f p Ω`: `f ∈ L^p_loc (Ω)`, that is, `f ∈ L^p (K)` for every compact
  `K ⊆ Ω`.
* `HarmonicAnalysis.HasWeakLineDerivOn Ω f g v`: `g` is a weak derivative of `f` in the
  direction `v` on `Ω`, that is, `∫ (∂_v φ) f = −∫ φ g` for every real `φ ∈ C_c^∞ (E)` with
  `tsupport φ ⊆ Ω`.
* `HarmonicAnalysis.HasWeakFDerivOn Ω f Df`: `Df : E → (E →L[ℝ] F)` is a weak derivative of `f`
  on `Ω`: for every `v`, `x ↦ Df x v` is a weak derivative of `f` in the direction `v`.

The integrals are Bochner integrals, so the definitions are meant for a complete `F`: for an
incomplete `F`, Mathlib's integral is `0` and every `g` would be a weak derivative. The theorems of
the package use them with `F = ℂ` and `F = ℂ →L[ℝ] ℂ`.

The local Sobolev space `W^{1,p}_loc (Ω)` is that of the `f ∈ L^p_loc (Ω)` with a weak derivative
`Df ∈ L^p_loc (Ω)`; the theorems take the three conditions `MemLpLoc f p Ω`,
`HasWeakFDerivOn Ω f Df` and `MemLpLoc Df p Ω`. This is the standard definition (weak partial
derivatives in `L^p_loc`): for `E = ℝⁿ`, `Df x` is determined by the partial derivatives
`Df x eᵢ`, and `‖Df x‖` is equivalent to `Σᵢ ‖Df x eᵢ‖`. The test functions are real-valued; for
complex `f` this is equivalent to complex-valued test functions, by linearity.

On the plane, `HarmonicAnalysis.dzPart A = ½ (A 1 − i A i)` and
`HarmonicAnalysis.dzbarPart A = ½ (A 1 + i A i)` are the complex-linear and the
complex-antilinear parts of a real-linear map `A : ℂ → ℂ`:
`A v = (dzPart A) v + (dzbarPart A) (conj v)`;
for `A = Df (z)` they are the Wirtinger derivatives `∂f (z)` and `∂_zbar f (z)`.

## Main results

* `HarmonicAnalysis.HasWeakLineDerivOn.ae_eq`: weak derivatives are unique almost everywhere.
* `HarmonicAnalysis.HasWeakFDerivOn.smul_of_tsupport_subset`: for a smooth `η` with compact
  support in `Ω`, `η f` has the weak derivative `η Df + Dη ⊗ f` on the whole space (the Leibniz
  rule).
* `HarmonicAnalysis.MemLpLoc.memLp_smul_of_tsupport_subset`: `η f ∈ L^p` for such `η`.
* `HarmonicAnalysis.apply_eq_dzPart_add_dzbarPart`, `HarmonicAnalysis.norm_le_dzPart_add_dzbarPart`.

## Proofs

* The integrability of `φ g` for `g` locally integrable on `Ω` and a continuous `φ` with compact
  support in `Ω` (`HarmonicAnalysis.sob_integrable_smul_of_tsupport_subset`) makes the integrals of
  the weak-derivative identities split.
* Uniqueness: the difference of two weak derivatives integrates to `0` against every test function,
  and Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` applies.
* The Leibniz rule: the weak-derivative identity of `f` is tested against `φ η`, whose derivative is
  `(∂_v φ) η + φ ∂_v η`; the openness of `Ω` is not used.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff ComplexConjugate

namespace HarmonicAnalysis

section Defs

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `f ∈ L^p_loc (Ω)`: `f ∈ L^p (K)` for every compact `K ⊆ Ω`. -/
def MemLpLoc (f : E → F) (p : ℝ≥0∞) (Ω : Set E) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → MemLp f p (volume.restrict K)

/-- `g` is a weak derivative of `f` in the direction `v` on `Ω`: `∫ (∂_v φ) f = −∫ φ g` for every
real `φ ∈ C_c^∞ (E)` with `tsupport φ ⊆ Ω`. -/
def HasWeakLineDerivOn (Ω : Set E) (f g : E → F) (v : E) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∫ x, fderiv ℝ φ x v • f x = -∫ x, φ x • g x

/-- `Df` is a weak derivative of `f` on `Ω`: for every `v`, `x ↦ Df x v` is a weak derivative of
`f` in the direction `v` on `Ω`. -/
def HasWeakFDerivOn (Ω : Set E) (f : E → F) (Df : E → E →L[ℝ] F) : Prop :=
  ∀ v, HasWeakLineDerivOn Ω f (fun x => Df x v) v

theorem HasWeakFDerivOn.mono {Ω Ω' : Set E} {f : E → F} {Df : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn Ω f Df) (hΩ : Ω' ⊆ Ω) : HasWeakFDerivOn Ω' f Df :=
  fun v φ hφ hφc hφΩ => h v φ hφ hφc (hφΩ.trans hΩ)

end Defs

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedSpace ℝ F]
  [CompleteSpace F] in
/-- `L^q_loc ⊆ L^p_loc` for `p ≤ q`: compact sets have finite measure. -/
theorem MemLpLoc.mono_exponent {Ω : Set E} {f : E → F} {p q : ℝ≥0∞} (hpq : p ≤ q)
    (h : MemLpLoc f q Ω) : MemLpLoc f p Ω := by
  intro K hKΩ hK
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  exact (h K hKΩ hK).mono_exponent hpq

omit [BorelSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- A function in `L^p_loc (Ω)`, `1 ≤ p`, is locally integrable on the open set `Ω`. -/
theorem MemLpLoc.locallyIntegrableOn {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (h : MemLpLoc f p Ω) : LocallyIntegrableOn f Ω volume := by
  rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
  intro K hKΩ hK
  exact memLp_one_iff_integrable.1 ((h.mono_exponent hp) K hKΩ hK)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsFiniteMeasureOnCompacts (volume : Measure E)]
  [CompleteSpace F] in
/-- `η f ∈ L^p` for `f ∈ L^p_loc (Ω)` and a continuous `η` with compact support in `Ω`. -/
theorem MemLpLoc.memLp_smul_of_tsupport_subset {Ω : Set E} {f : E → F} {p : ℝ≥0∞}
    (h : MemLpLoc f p Ω) {η : E → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) : MemLp (fun x => η x • f x) p volume := by
  obtain ⟨C, hC⟩ := hη.bounded_above_of_compact_support hηc
  have hfK := h _ hηΩ hηc
  have heq : (tsupport η).indicator (fun x => η x • f x) = fun x => η x • f x :=
    Set.indicator_eq_self.2 fun x hx =>
      subset_tsupport η (Function.support_smul_subset_left η f hx)
  rw [← heq, memLp_indicator_iff_restrict (isClosed_tsupport η).measurableSet.nullMeasurableSet]
  refine hfK.of_le_mul (c := C) (hη.aestronglyMeasurable.smul hfK.aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- `φ g` is integrable for `g` locally integrable on `Ω` and a continuous real `φ` with compact
support in `Ω`. -/
theorem sob_integrable_smul_of_tsupport_subset {X G : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure X} {Ω : Set X} {g : X → G} (hg : LocallyIntegrableOn g Ω μ) {φ : X → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    Integrable (fun x => φ x • g x) μ := by
  have h₁ : IntegrableOn (fun x => φ x • g x) (tsupport φ) μ :=
    (hg.integrableOn_compact_subset hφΩ hφc).continuousOn_smul hφ.continuousOn hφc
  exact (integrableOn_iff_integrable_of_support_subset (f := fun x => φ x • g x)
    fun x hx => subset_tsupport φ (Function.support_smul_subset_left φ g hx)).1 h₁

omit [IsFiniteMeasureOnCompacts (volume : Measure E)] in
/-- Weak derivatives are unique: two weak derivatives of `f` in the direction `v` on the open set
`Ω`, both locally integrable on `Ω`, agree almost everywhere on `Ω` (the fundamental lemma of the
calculus of variations, `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
theorem HasWeakLineDerivOn.ae_eq {Ω : Set E} (hΩ : IsOpen Ω) {f g₁ g₂ : E → F} {v : E}
    (h₁ : HasWeakLineDerivOn Ω f g₁ v) (h₂ : HasWeakLineDerivOn Ω f g₂ v)
    (hg₁ : LocallyIntegrableOn g₁ Ω volume) (hg₂ : LocallyIntegrableOn g₂ Ω volume) :
    g₁ =ᵐ[volume.restrict Ω] g₂ := by
  have key := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hg₁.sub hg₂)
    (fun φ hφ hφc hφΩ => by
      have i₁ := sob_integrable_smul_of_tsupport_subset hg₁ hφ.continuous hφc hφΩ
      have i₂ := sob_integrable_smul_of_tsupport_subset hg₂ hφ.continuous hφc hφΩ
      simp only [Pi.sub_apply, smul_sub]
      rw [integral_sub i₁ i₂, sub_eq_zero, ← neg_inj, ← h₁ φ hφ hφc hφΩ, h₂ φ hφ hφc hφΩ])
  rw [Filter.EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
  filter_upwards [key] with x hx hxΩ
  exact sub_eq_zero.1 (hx hxΩ)

omit [FiniteDimensional ℝ E] [IsFiniteMeasureOnCompacts (volume : Measure E)] [CompleteSpace F] in
/-- **The Leibniz rule with a cut-off.** If `Df` is a weak derivative of `f` on `Ω` (both locally
integrable on `Ω`) and `η ∈ C_c^∞ (E)` is real with `tsupport η ⊆ Ω`, then `η f`
has the weak derivative `η Df + Dη ⊗ f`, `v ↦ η (x) Df (x) v + (∂_v η (x)) f (x)`, on the whole
space. -/
theorem HasWeakFDerivOn.smul_of_tsupport_subset {Ω : Set E} {f : E → F} {Df : E → E →L[ℝ] F}
    (hf : LocallyIntegrableOn f Ω volume) (hDf : LocallyIntegrableOn Df Ω volume)
    (h : HasWeakFDerivOn Ω f Df) {η : E → ℝ}
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω) :
    HasWeakFDerivOn Set.univ (fun x => η x • f x)
      (fun x => η x • Df x + (fderiv ℝ η x).smulRight (f x)) := by
  intro v φ hφ hφc _
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hηd : Differentiable ℝ η := hη.differentiable (by simp)
  have hDφ : Continuous fun x => fderiv ℝ φ x v :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDη : Continuous fun x => fderiv ℝ η x v :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDηΩ : tsupport (fun x => fderiv ℝ η x v) ⊆ tsupport η := tsupport_fderiv_apply_subset ℝ v
  -- the test function `φ η`
  have hψ : ContDiff ℝ ∞ (fun x => φ x * η x) := hφ.mul hη
  have hψc : HasCompactSupport (fun x => φ x * η x) := hηc.mul_left
  have hψΩ : tsupport (fun x => φ x * η x) ⊆ Ω := tsupport_mul_subset_right.trans hηΩ
  have key := h v _ hψ hψc hψΩ
  have hderiv : ∀ x, fderiv ℝ (fun x => φ x * η x) x v =
      φ x * fderiv ℝ η x v + η x * fderiv ℝ φ x v := by
    intro x
    rw [fderiv_fun_mul (hφd x) (hηd x)]
    simp [smul_eq_mul]
  have i₁ : Integrable (fun x => (φ x * fderiv ℝ η x v) • f x) :=
    sob_integrable_smul_of_tsupport_subset hf (hφ.continuous.mul hDη)
      ((hηc.fderiv_apply (𝕜 := ℝ) v).mul_left)
      (tsupport_mul_subset_right.trans (hDηΩ.trans hηΩ))
  have i₂ : Integrable (fun x => (η x * fderiv ℝ φ x v) • f x) :=
    sob_integrable_smul_of_tsupport_subset hf (hη.continuous.mul hDφ) hηc.mul_right
      (tsupport_mul_subset_left.trans hηΩ)
  have i₃ : Integrable (fun x => (φ x * η x) • Df x v) :=
    (sob_integrable_smul_of_tsupport_subset hDf (hφ.continuous.mul hη.continuous) hψc
      hψΩ).apply_continuousLinearMap v
  simp only [hderiv, add_smul] at key
  rw [integral_add i₁ i₂] at key
  have e₁ : (fun x => fderiv ℝ φ x v • η x • f x) = fun x => (η x * fderiv ℝ φ x v) • f x := by
    ext x; rw [smul_smul, mul_comm]
  have e₂ : (fun x => φ x • (η x • Df x + (fderiv ℝ η x).smulRight (f x)) v) =
      fun x => (φ x * η x) • Df x v + (φ x * fderiv ℝ η x v) • f x := by
    ext x; simp [smul_add, smul_smul]
  simp only [e₁, e₂]
  rw [integral_add i₃ i₁, neg_add, ← key]
  abel

end General

/-! ### The Wirtinger parts of a real-linear map of `ℂ` -/

section Wirtinger

/-- The complex-linear part `½ (A 1 − i A i)` of a real-linear map `A : ℂ → ℂ`; for `A = Df (z)`
it is the Wirtinger derivative `∂f (z)`. -/
def dzPart (A : ℂ →L[ℝ] ℂ) : ℂ := (2⁻¹ : ℂ) * (A 1 - Complex.I * A Complex.I)

/-- The complex-antilinear part `½ (A 1 + i A i)` of a real-linear map `A : ℂ → ℂ`; for
`A = Df (z)` it is the Wirtinger derivative `∂_zbar f (z)`. -/
def dzbarPart (A : ℂ →L[ℝ] ℂ) : ℂ := (2⁻¹ : ℂ) * (A 1 + Complex.I * A Complex.I)

/-- `A v = (∂A) v + (∂_zbar A) (conj v)`. -/
theorem apply_eq_dzPart_add_dzbarPart (A : ℂ →L[ℝ] ℂ) (v : ℂ) :
    A v = dzPart A * v + dzbarPart A * conj v := by
  have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
    simp [Complex.real_smul, Complex.re_add_im]
  have hcv : conj v = (v.re : ℂ) - v.im * Complex.I := Complex.ext (by simp) (by simp)
  have hv' : v = (v.re : ℂ) + v.im * Complex.I := (Complex.re_add_im v).symm
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, hcv, Complex.real_smul, Complex.real_smul]
  simp only [dzPart, dzbarPart]
  linear_combination (-(2⁻¹ * (A 1 - Complex.I * A Complex.I))) * hv' +
    (A Complex.I * v.im) * Complex.I_sq

/-- `‖A‖ ≤ |∂A| + |∂_zbar A|` (in fact `=`). -/
theorem norm_le_dzPart_add_dzbarPart (A : ℂ →L[ℝ] ℂ) : ‖A‖ ≤ ‖dzPart A‖ + ‖dzbarPart A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [apply_eq_dzPart_add_dzbarPart, add_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_conj]

/-- `|∂A| ≤ ‖A‖`. -/
theorem norm_dzPart_le (A : ℂ →L[ℝ] ℂ) : ‖dzPart A‖ ≤ ‖A‖ := by
  have h₁ : ‖A 1‖ ≤ ‖A‖ := by simpa using A.le_opNorm 1
  have hI : ‖A Complex.I‖ ≤ ‖A‖ := by simpa using A.le_opNorm Complex.I
  calc ‖dzPart A‖ ≤ 2⁻¹ * (‖A 1‖ + ‖A Complex.I‖) := by
        rw [dzPart, norm_mul]
        gcongr
        · simp
        · exact (norm_sub_le _ _).trans (by simp)
    _ ≤ ‖A‖ := by linarith

/-- `|∂_zbar A| ≤ ‖A‖`. -/
theorem norm_dzbarPart_le (A : ℂ →L[ℝ] ℂ) : ‖dzbarPart A‖ ≤ ‖A‖ := by
  have h₁ : ‖A 1‖ ≤ ‖A‖ := by simpa using A.le_opNorm 1
  have hI : ‖A Complex.I‖ ≤ ‖A‖ := by simpa using A.le_opNorm Complex.I
  calc ‖dzbarPart A‖ ≤ 2⁻¹ * (‖A 1‖ + ‖A Complex.I‖) := by
        rw [dzbarPart, norm_mul]
        gcongr
        · simp
        · exact (norm_add_le _ _).trans (by simp)
    _ ≤ ‖A‖ := by linarith

/-- `∂` of the derivative is the Wirtinger derivative `HarmonicAnalysis.dz`. -/
theorem dzPart_fderiv (g : ℂ → ℂ) (z : ℂ) : dzPart (fderiv ℝ g z) = dz g z := by
  simp only [dzPart, dz, smul_eq_mul]

/-- `∂_zbar` of the derivative is the Wirtinger derivative `HarmonicAnalysis.dzbar`. -/
theorem dzbarPart_fderiv (g : ℂ → ℂ) (z : ℂ) : dzbarPart (fderiv ℝ g z) = dzbar g z := by
  simp only [dzbarPart, dzbar, smul_eq_mul]

/-- `A ↦ ∂A` is continuous. -/
theorem continuous_dzPart : Continuous dzPart := by
  unfold dzPart
  fun_prop

/-- `A ↦ ∂_zbar A` is continuous. -/
theorem continuous_dzbarPart : Continuous dzbarPart := by
  unfold dzbarPart
  fun_prop

/-- `∂ (Df) ∈ L^p` for `Df ∈ L^p`. -/
theorem memLp_dzPart {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {Df : α → ℂ →L[ℝ] ℂ} (h : MemLp Df p μ) : MemLp (fun x => dzPart (Df x)) p μ :=
  h.of_le (continuous_dzPart.comp_aestronglyMeasurable h.aestronglyMeasurable)
    (ae_of_all _ fun x => norm_dzPart_le (Df x))

/-- `∂_zbar (Df) ∈ L^p` for `Df ∈ L^p`. -/
theorem memLp_dzbarPart {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {Df : α → ℂ →L[ℝ] ℂ} (h : MemLp Df p μ) : MemLp (fun x => dzbarPart (Df x)) p μ :=
  h.of_le (continuous_dzbarPart.comp_aestronglyMeasurable h.aestronglyMeasurable)
    (ae_of_all _ fun x => norm_dzbarPart_le (Df x))

end Wirtinger

end HarmonicAnalysis

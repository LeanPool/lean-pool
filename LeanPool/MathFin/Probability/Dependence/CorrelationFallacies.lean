/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.NormalQuantile
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Normal margins and zero correlation determine neither independence nor normality

Embrechts, McNeil and Straumann (2002) list the fallacies that come from reading linear correlation
as a complete description of dependence. The standard counterexample (QRM Exercise Book
Ex. 6.1 and 6.18; McNeil–Frey–Embrechts (2015), Fallacy 1) is a standard normal `Z` and an
independent random sign `V`, `P(V = 1) = P(V = −1) = 1/2`, combined as `Y = V Z`. Then:

* `Y` is standard normal (`hasLaw_mul_gaussianReal`), because a random sign times a symmetric
  variable keeps its law (`rademacher_mconv_of_map_neg`);
* `cov(Z, Y) = 0` (`covariance_mul_eq_zero`);
* `Z` and `Y` are **not independent** (`not_indepFun_mul`), since `|Y| = |Z|`;
* `Z + Y` is **not Gaussian** (`not_hasLaw_add_mul_gaussianReal`). It vanishes exactly when
  `V = −1`, which has probability `1/2`, whereas a Gaussian law gives the point `0` mass `0` or
  `1`;
* hence `(Z, Y)` is **not jointly Gaussian** (`not_hasGaussianLaw_prod`), although both margins
  are: for a jointly Gaussian pair, zero covariance would force independence
  (Mathlib's `HasGaussianLaw.indepFun_of_covariance_eq_zero`).

So margins together with the correlation do not determine the joint law. Two variables can be
standard normal and uncorrelated without being independent, and without their sum being normal.
Such a pair exists (`exists_gaussian_uncorrelated_not_indepFun`).

## Main definitions

* `rademacher`: the law of a fair random sign, `±1` each with probability `1/2`.

## Main results

* `rademacher_mconv_of_map_neg`: a random sign times an independent symmetric variable has the
  same law as the variable.
* `hasLaw_mul_gaussianReal`, `covariance_mul_eq_zero`, `not_indepFun_mul`,
  `not_hasLaw_add_mul_gaussianReal`, `not_hasGaussianLaw_prod`: the counterexample.
* `exists_gaussian_uncorrelated_not_indepFun`: the counterexample is realized.

## References

* [Embrechts, McNeil and Straumann (2002)][EmbrechtsMcNeilStraumann2002]
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 6.1, 6.18

## Tags

correlation fallacy, uncorrelated not independent, joint normality, dependence,
Embrechts–McNeil–Straumann, random sign, MSC 62H05, MSC 60E05, MSC 91G70
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The **Rademacher law** of a fair random sign: `±1`, each with probability `1/2`. -/
noncomputable def rademacher : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 1 + Measure.dirac (-1))

instance isProbabilityMeasure_rademacher : IsProbabilityMeasure rademacher :=
  ⟨by simp [rademacher, ENNReal.inv_two_add_inv_two]⟩

/-- A random sign has mean zero. -/
lemma integral_id_rademacher : ∫ x, x ∂rademacher = 0 := by
  rw [rademacher, integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  simp

/-- A random sign is almost surely `±1`. -/
lemma ae_rademacher : ∀ᵐ x ∂rademacher, x = 1 ∨ x = -1 := by
  rw [ae_iff]
  simp [rademacher, Measure.dirac_apply]

/-- A random sign takes the value `-1` with probability `1/2`. -/
lemma rademacher_singleton_neg_one : rademacher {-1} = 2⁻¹ := by
  simp [rademacher, show (1 : ℝ) ≠ -1 by norm_num]

/-- **A random sign times an independent symmetric variable keeps its law**: if `μ` is symmetric,
`μ.map (−·) = μ`, then the multiplicative convolution of the Rademacher law with `μ` is `μ`. -/
theorem rademacher_mconv_of_map_neg {μ : Measure ℝ} [SFinite μ]
    (hμ : μ.map (fun x ↦ -x) = μ) : rademacher ∗ₘ μ = μ := by
  rw [rademacher, Measure.mconv_smul_left, Measure.add_mconv, Measure.dirac_mconv,
    Measure.dirac_mconv]
  simp only [one_mul, neg_one_mul, Measure.map_id', hμ]
  rw [← two_smul ℝ≥0∞ μ, smul_smul, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Z V : Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- A variable with the Rademacher law is almost surely `±1`. -/
private lemma ae_eq_one_or_neg_one (hV : HasLaw V rademacher P) :
    ∀ᵐ ω ∂P, V ω = 1 ∨ V ω = -1 :=
  (hV.ae_iff (p := fun x ↦ x = 1 ∨ x = -1) (measurableSet_setOfPred.1
    ((measurableSet_singleton 1).union (measurableSet_singleton (-1))))).2 ae_rademacher

omit [IsProbabilityMeasure P] in
/-- `HasLaw` transfers the mass of a preimage; Mathlib's `HasLaw.measureReal_eq` is stated for
set-builder events, and the proofs below work with preimages. -/
lemma measureReal_preimage_of_hasLaw {X : Ω → ℝ} {μ : Measure ℝ} (hX : HasLaw X μ P)
    {s : Set ℝ} (hs : MeasurableSet s) : P.real (X ⁻¹' s) = μ.real s := by
  rw [← map_measureReal_apply_of_aemeasurable hX.aemeasurable hs, hX.map_eq]

omit [IsProbabilityMeasure P] in
/-- **`Y = V Z` is standard normal**: a random sign times an independent standard normal
variable. -/
theorem hasLaw_mul_gaussianReal (hZ : HasLaw Z (gaussianReal 0 1) P) (hV : HasLaw V rademacher P)
    (hVZ : V ⟂ᵢ[P] Z) : HasLaw (fun ω ↦ V ω * Z ω) (gaussianReal 0 1) P := by
  have h := hVZ.hasLaw_fun_mul hV hZ
  rwa [rademacher_mconv_of_map_neg (μ := gaussianReal 0 1)
    (by rw [gaussianReal_map_neg, neg_zero])] at h

/-- **Zero correlation**: `cov(Z, V Z) = 0`, since `E[Z · V Z] = E[V] E[Z²] = 0`. -/
theorem covariance_mul_eq_zero (hZ : HasLaw Z (gaussianReal 0 1) P) (hV : HasLaw V rademacher P)
    (hVZ : V ⟂ᵢ[P] Z) : cov[Z, fun ω ↦ V ω * Z ω; P] = 0 := by
  have hY := hasLaw_mul_gaussianReal hZ hV hVZ
  have hEV : P[V] = 0 := by rw [hV.integral_eq, integral_id_rademacher]
  have hEZ : P[Z] = 0 := by rw [hZ.integral_eq, integral_id_gaussianReal]
  have hind : V ⟂ᵢ[P] (fun ω ↦ Z ω * Z ω) :=
    hVZ.comp (φ := id) (ψ := fun z ↦ z * z) measurable_id (measurable_id.mul measurable_id)
  rw [covariance_eq_sub hZ.hasGaussianLaw.memLp_two
    hY.hasGaussianLaw.memLp_two, hEZ, zero_mul, sub_zero]
  calc P[Z * fun ω ↦ V ω * Z ω] = ∫ ω, V ω * (Z ω * Z ω) ∂P := by
        congr 1; ext ω; simp only [Pi.mul_apply]; ring
    _ = P[V] * ∫ ω, Z ω * Z ω ∂P :=
        hind.integral_fun_mul_eq_mul_integral hV.aemeasurable.aestronglyMeasurable
          (hZ.aemeasurable.mul hZ.aemeasurable).aestronglyMeasurable
    _ = 0 := by rw [hEV, zero_mul]

omit [IsProbabilityMeasure P] in
/-- `|V Z| = |Z|` almost surely. -/
private lemma ae_abs_mul_eq (hV : HasLaw V rademacher P) :
    ∀ᵐ ω ∂P, |V ω * Z ω| = |Z ω| := by
  filter_upwards [ae_eq_one_or_neg_one hV] with ω hω
  rcases hω with h1 | h1 <;> simp [h1]

/-- The standard normal law puts mass strictly between `0` and `1` on `[-1, 1]`. -/
lemma gaussianReal_Icc_mem_Ioo :
    (gaussianReal 0 1).real (Icc (-1) 1) ∈ Ioo 0 1 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hIoc : (gaussianReal 0 1).real (Icc (-1) 1) = Phi 1 - Phi (-1) := by
    rw [measureReal_def, ← measure_congr (Ioc_ae_eq_Icc (μ := gaussianReal 0 1)),
      ← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.2 (monotone_cdf _ (by norm_num))),
      cdf_gaussianReal_zero_one]
  rw [hIoc]
  exact ⟨sub_pos.2 (strictMono_Phi (by norm_num)),
    by linarith [(Phi_mem_Ioo 1).2, (Phi_mem_Ioo (-1)).1]⟩

omit [IsProbabilityMeasure P] in
/-- **`Z` and `V Z` are not independent**, though uncorrelated: they share the absolute value,
so `P(|Z| ≤ 1, |V Z| ≤ 1) = P(|Z| ≤ 1) ≠ P(|Z| ≤ 1)²`. -/
theorem not_indepFun_mul (hZ : HasLaw Z (gaussianReal 0 1) P) (hV : HasLaw V rademacher P) :
    ¬ Z ⟂ᵢ[P] (fun ω ↦ V ω * Z ω) := by
  intro hind
  have hS : MeasurableSet (Icc (-1 : ℝ) 1) := measurableSet_Icc
  have hiff : ∀ᵐ ω ∂P, (V ω * Z ω ∈ Icc (-1 : ℝ) 1 ↔ Z ω ∈ Icc (-1 : ℝ) 1) := by
    filter_upwards [ae_abs_mul_eq (Z := Z) hV] with ω hω
    rw [mem_Icc, mem_Icc, ← abs_le, ← abs_le, hω]
  have hsame : (fun ω ↦ V ω * Z ω) ⁻¹' Icc (-1) 1 =ᵐ[P] Z ⁻¹' Icc (-1) 1 := by
    filter_upwards [hiff] with ω hω
    exact hω
  have hinter : (Z ⁻¹' Icc (-1) 1 ∩ (fun ω ↦ V ω * Z ω) ⁻¹' Icc (-1) 1 : Set Ω)
      =ᵐ[P] Z ⁻¹' Icc (-1) 1 := by
    filter_upwards [hiff] with ω hω
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hω.2 h⟩⟩
  have h := hind.measure_inter_preimage_eq_mul _ _ hS hS
  rw [measure_congr hinter, measure_congr hsame] at h
  have hc : P.real (Z ⁻¹' Icc (-1) 1) ∈ Ioo 0 1 := by
    rw [measureReal_preimage_of_hasLaw hZ hS]
    exact gaussianReal_Icc_mem_Ioo
  have h' : P.real (Z ⁻¹' Icc (-1) 1)
      = P.real (Z ⁻¹' Icc (-1) 1) * P.real (Z ⁻¹' Icc (-1) 1) := by
    simp only [measureReal_def]
    rw [← ENNReal.toReal_mul, ← h]
  nlinarith [mul_pos hc.1 (sub_pos.2 hc.2)]

/-- `Z + V Z` vanishes with probability exactly `1/2`: on `{V = −1}`, and otherwise only where
`Z = 0`, a null event. -/
private lemma measureReal_add_mul_eq_zero (hZ : HasLaw Z (gaussianReal 0 1) P)
    (hV : HasLaw V rademacher P) : P.real {ω | Z ω + V ω * Z ω = 0} = 2⁻¹ := by
  have hset : {ω | Z ω + V ω * Z ω = 0} =ᵐ[P] (V ⁻¹' {-1} ∪ Z ⁻¹' {0} : Set Ω) := by
    filter_upwards [ae_eq_one_or_neg_one hV] with ω hω
    rcases hω with h1 | h1 <;> simp [h1, show (1 : ℝ) ≠ -1 by norm_num]
  have hV1 : P.real (V ⁻¹' {-1}) = 2⁻¹ := by
    rw [measureReal_preimage_of_hasLaw hV (measurableSet_singleton _), measureReal_def,
      rademacher_singleton_neg_one]
    simp
  have hZ0 : P.real (Z ⁻¹' {0}) = 0 := by
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    rw [measureReal_preimage_of_hasLaw hZ (measurableSet_singleton _)]
    simp [measureReal_def]
  rw [measureReal_congr hset]
  refine le_antisymm ((measureReal_union_le _ _).trans (by rw [hV1, hZ0, add_zero])) ?_
  rw [← hV1]
  exact measureReal_mono subset_union_left

/-- **`Z + V Z` is not Gaussian**: it has an atom of mass `1/2` at `0`, while a Gaussian law gives
the point `0` mass `0` (positive variance) or `0` or `1` (a point mass). -/
theorem not_hasLaw_add_mul_gaussianReal (hZ : HasLaw Z (gaussianReal 0 1) P)
    (hV : HasLaw V rademacher P) :
    ¬ ∃ m v, HasLaw (fun ω ↦ Z ω + V ω * Z ω) (gaussianReal m v) P := by
  rintro ⟨m, v, hS⟩
  have h := measureReal_add_mul_eq_zero hZ hV
  rw [show {ω | Z ω + V ω * Z ω = 0} = (fun ω ↦ Z ω + V ω * Z ω) ⁻¹' {0} from rfl,
    measureReal_preimage_of_hasLaw hS (measurableSet_singleton _)] at h
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var] at h
    by_cases hm : m = 0 <;> simp [measureReal_def, hm] at h
  · have := nullSingletonClass_gaussianReal (μ := m) hv
    simp [measureReal_def] at h

/-- **`(Z, V Z)` is not jointly Gaussian**, although both margins are standard normal: a jointly
Gaussian pair with zero covariance is independent
(`HasGaussianLaw.indepFun_of_covariance_eq_zero`), and `Z`, `V Z` are uncorrelated but
dependent. -/
theorem not_hasGaussianLaw_prod (hZ : HasLaw Z (gaussianReal 0 1) P) (hV : HasLaw V rademacher P)
    (hVZ : V ⟂ᵢ[P] Z) : ¬ HasGaussianLaw (fun ω ↦ (Z ω, V ω * Z ω)) P := fun h ↦
  not_indepFun_mul hZ hV <| h.indepFun_of_covariance_eq_zero (covariance_mul_eq_zero hZ hV hVZ)

/-- **The correlation fallacy is realized**: there are two standard normal random variables that
are uncorrelated, not independent, not jointly Gaussian, and whose sum is not Gaussian. -/
theorem exists_gaussian_uncorrelated_not_indepFun :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z Y : Ω → ℝ),
      IsProbabilityMeasure P ∧ HasLaw Z (gaussianReal 0 1) P ∧ HasLaw Y (gaussianReal 0 1) P ∧
      cov[Z, Y; P] = 0 ∧ ¬ Z ⟂ᵢ[P] Y ∧ ¬ HasGaussianLaw (fun ω ↦ (Z ω, Y ω)) P ∧
      ¬ ∃ m v, HasLaw (fun ω ↦ Z ω + Y ω) (gaussianReal m v) P := by
  have hV : HasLaw Prod.fst rademacher (rademacher.prod (gaussianReal 0 1)) :=
    ⟨measurable_fst.aemeasurable, by simp⟩
  have hZ : HasLaw Prod.snd (gaussianReal 0 1) (rademacher.prod (gaussianReal 0 1)) :=
    ⟨measurable_snd.aemeasurable, by simp⟩
  have hVZ : (Prod.fst : ℝ × ℝ → ℝ) ⟂ᵢ[rademacher.prod (gaussianReal 0 1)] Prod.snd :=
    indepFun_prod measurable_id measurable_id
  exact ⟨ℝ × ℝ, inferInstance, rademacher.prod (gaussianReal 0 1), Prod.snd, fun ω ↦ ω.1 * ω.2,
    inferInstance, hZ,
    hasLaw_mul_gaussianReal hZ hV hVZ, covariance_mul_eq_zero hZ hV hVZ, not_indepFun_mul hZ hV,
    not_hasGaussianLaw_prod hZ hV hVZ, not_hasLaw_add_mul_gaussianReal hZ hV⟩

end MathFin

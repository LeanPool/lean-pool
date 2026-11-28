/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Dependence.Copula
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Copula families: Farlie–Gumbel–Morgenstern and Clayton

Two parametric bivariate families from McNeil–Frey–Embrechts, *Quantitative Risk Management*
(2015), Chapter 7, and the QRM Exercise Book, Exercises 7.17 and 7.19.

**Farlie–Gumbel–Morgenstern.** The FGM copula `fgmCopula θ` is the law on the unit square with
density `1 + θ(1 − 2u)(1 − 2v)` against the independence copula. For `|θ| ≤ 1` it is a copula
(`isCopula_fgmCopula`) with distribution function `uv + θ uv(1 − u)(1 − v)`
(`fgmCopula_real_Iic`). For `|θ| > 1` no copula has that distribution function, so
`|θ| ≤ 1` is exactly the admissible range (`exists_isCopula_fgm_iff`). A negative-mass rectangle
near a corner of the square rules out the other values. Its Spearman's rho is `θ/3`
(`spearmanRho_fgmCopula`), so the family only reaches rank correlations in `[−1/3, 1/3]`. This is
the drawback the exercise asks about: FGM can model only weak dependence.

**Clayton.** The Clayton copula function `C_θ(u, v) = (u^{−θ} + v^{−θ} − 1)^{−1/θ}` is treated at
the level of the function. This file proves its coefficient of lower tail dependence,
`lim_{u → 0⁺} C_θ(u, u)/u = 2^{−1/θ}` (`tendsto_claytonCopulaFun_diag_div`), and its limits in the
parameter: the independence copula `uv` as `θ → 0⁺` (`tendsto_claytonCopulaFun_zero`) and the
comonotonicity copula `min(u, v)` as `θ → ∞` (`tendsto_claytonCopulaFun_atTop`). That
`C_θ` is the distribution function of a copula (the Archimedean-generator or gamma-frailty
construction) is **not** proved here.

**Spearman's rho** of a bivariate copula is the linear correlation of its two uniform coordinates
(`spearmanRho`). For a random vector with continuous margins it is Spearman's rho of the vector,
computed on its copula (MFE Definition 7.33). Under a copula it equals `12 E[U₀U₁] − 3`
(`IsCopula.spearmanRho_eq`).

## Main definitions

* `spearmanRho`: Spearman's rank correlation of a bivariate copula.
* `fgmDensity`: the Farlie–Gumbel–Morgenstern density `1 + θ(1 − 2u)(1 − 2v)`.
* `fgmCopula`: the Farlie–Gumbel–Morgenstern copula, the law with density `fgmDensity θ` against
  the independence copula.
* `claytonCopulaFun`: the Clayton copula function `C_θ(u, v) = (u^{−θ} + v^{−θ} − 1)^{−1/θ}`.

## Main results

* `IsCopula.spearmanRho_eq`: `ρ_S = 12 E[U₀U₁] − 3` for every bivariate copula.
* `isCopula_fgmCopula`, `fgmCopula_real_Iic`: the FGM copula and its distribution function.
* `exists_isCopula_fgm_iff`: `uv + θuv(1 − u)(1 − v)` is a copula exactly when `|θ| ≤ 1`.
* `spearmanRho_fgmCopula`: `ρ_S = θ/3`.
* `tendsto_claytonCopulaFun_diag_div`: Clayton lower tail dependence `λ_l = 2^{−1/θ}`.
* `tendsto_claytonCopulaFun_zero`, `tendsto_claytonCopulaFun_atTop`: the limits `Π` and `M`.

## References

* [*QRM Exercise Book*][QRMExerciseBook], Ex. 7.17(b); Ex. 7.19(a); Ex. 7.19(d)

## Tags

Farlie–Gumbel–Morgenstern copula, Clayton copula, tail dependence, Spearman's rho, rank correlation,
Archimedean copula, MSC 62H05, MSC 91G70
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter Topology

/-! ### Integrals against the uniform law on `(0, 1)` -/

/-- Integrals over the uniform law on `(0, 1)` are interval integrals over `[0, 1]`. -/
lemma integral_uniformIoo (f : ℝ → ℝ) :
    ∫ x, f x ∂(volume.restrict (Ioo 0 1)) = ∫ x in (0 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- Integrals over `(-∞, t]` against the uniform law on `(0, 1)` are interval integrals over
`[0, t]` for `t ∈ [0, 1]`. -/
lemma setIntegral_uniformIoo_Iic (f : ℝ → ℝ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ∫ x in Iic t, f x ∂(volume.restrict (Ioo 0 1)) = ∫ x in (0 : ℝ)..t, f x := by
  rw [Measure.restrict_restrict measurableSet_Iic, intervalIntegral.integral_of_le h0]
  rcases h1.lt_or_eq with h1 | rfl
  · rw [show Iic t ∩ Ioo 0 1 = Ioc 0 t by
      ext p; exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans_lt h1⟩⟩]
  · rw [inter_eq_right.2 (Ioo_subset_Ioc_self.trans Ioc_subset_Iic_self)]
    exact setIntegral_congr_set Ioo_ae_eq_Ioc

/-! ### Spearman's rho of a bivariate copula -/

/-- **Spearman's rank correlation** of a bivariate copula: the linear correlation of its two
uniform coordinates. For a random vector with continuous margins this is Spearman's rho of the
vector, `ρ_S(X₁, X₂) = ρ(F₁(X₁), F₂(X₂))`, computed on its copula. -/
noncomputable def spearmanRho (C : Measure (Fin 2 → ℝ)) : ℝ :=
  covariance (fun v ↦ v 0) (fun v ↦ v 1) C /
    √(variance (fun v ↦ v 0) C * variance (fun v ↦ v 1) C)

/-- Coordinates of a copula are square-integrable: they lie in `(0, 1)` almost surely. -/
lemma IsCopula.memLp_eval {ι : Type*} [Countable ι] {C : Measure (ι → ℝ)} (hC : IsCopula C)
    (i : ι) : MemLp (fun v : ι → ℝ ↦ v i) 2 C := by
  have := hC.isProbabilityMeasure
  refine MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable 1 ?_
  filter_upwards [hC.ae_mem_Ioo] with v hv
  rw [Real.norm_eq_abs, abs_of_pos (hv i).1]
  exact (hv i).2.le

/-- **Spearman's rho of a copula** is `12 E[U₀U₁] − 3`: each uniform coordinate has mean `1/2` and
variance `1/12`. -/
theorem IsCopula.spearmanRho_eq {C : Measure (Fin 2 → ℝ)} (hC : IsCopula C) :
    spearmanRho C = 12 * ∫ v, v 0 * v 1 ∂C - 3 := by
  have := hC.isProbabilityMeasure
  have hmean (i : Fin 2) : ∫ v, v i ∂C = 1 / 2 := by
    rw [show (fun v : Fin 2 → ℝ ↦ v i) = id ∘ fun v ↦ v i from rfl,
      (hC.hasLaw_eval i).integral_comp aestronglyMeasurable_id, integral_uniformIoo]
    simp [integral_id]
  have hsq (i : Fin 2) : ∫ v, (v i) ^ 2 ∂C = 1 / 3 := by
    rw [show (fun v : Fin 2 → ℝ ↦ (v i) ^ 2) = (fun x : ℝ ↦ x ^ 2) ∘ fun v ↦ v i from rfl,
      (hC.hasLaw_eval i).integral_comp (by fun_prop), integral_uniformIoo]
    simp [integral_pow]
    norm_num
  have hvar (i : Fin 2) : variance (fun v ↦ v i) C = 1 / 12 := by
    rw [variance_eq_sub (hC.memLp_eval i)]
    simp only [Pi.pow_apply]
    rw [hsq, hmean]
    norm_num
  rw [spearmanRho, covariance_eq_sub (hC.memLp_eval 0) (hC.memLp_eval 1), hvar, hvar]
  simp only [Pi.mul_apply]
  rw [hmean, hmean, show √((1 : ℝ) / 12 * (1 / 12)) = 1 / 12 by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]]
  ring

/-! ### The Farlie–Gumbel–Morgenstern copula -/

/-- The **Farlie–Gumbel–Morgenstern density** `1 + θ(1 − 2u)(1 − 2v)` on the unit square. -/
noncomputable def fgmDensity (θ : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  1 + θ * ((1 - 2 * v 0) * (1 - 2 * v 1))

/-- The **Farlie–Gumbel–Morgenstern copula**: density `1 + θ(1 − 2u)(1 − 2v)` against the
independence copula. It is a copula for `|θ| ≤ 1` (`isCopula_fgmCopula`). -/
noncomputable def fgmCopula (θ : ℝ) : Measure (Fin 2 → ℝ) :=
  (independenceCopula (Fin 2)).withDensity fun v ↦ ENNReal.ofReal (fgmDensity θ v)

variable {θ : ℝ}

lemma measurable_fgmDensity (θ : ℝ) : Measurable (fgmDensity θ) := by
  unfold fgmDensity; fun_prop

/-- The FGM density is nonnegative on the open unit square when `|θ| ≤ 1`. -/
lemma fgmDensity_nonneg (hθ : |θ| ≤ 1) {v : Fin 2 → ℝ} (hv : ∀ i, v i ∈ Ioo 0 1) :
    0 ≤ fgmDensity θ v := by
  have hb (i : Fin 2) : |1 - 2 * v i| ≤ 1 :=
      abs_le.2 ⟨by linarith [(hv i).2], by linarith [(hv i).1]⟩
  have hprod : |θ * ((1 - 2 * v 0) * (1 - 2 * v 1))| ≤ 1 := by
    rw [abs_mul, abs_mul]
    calc |θ| * (|1 - 2 * v 0| * |1 - 2 * v 1|) ≤ 1 * (1 * 1) := by
          gcongr
          exacts [hb 0, hb 1]
      _ = 1 := by norm_num
  unfold fgmDensity
  linarith [neg_abs_le (θ * ((1 - 2 * v 0) * (1 - 2 * v 1)))]

/-- Integrals of a product of one-coordinate functions against the independence copula
factor. -/
lemma integral_independenceCopula_two (f g : ℝ → ℝ) :
    ∫ v, f (v 0) * g (v 1) ∂(independenceCopula (Fin 2)) =
      (∫ x, f x ∂(volume.restrict (Ioo 0 1))) * ∫ x, g x ∂(volume.restrict (Ioo 0 1)) := by
  have h := integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (μ := fun _ : Fin 2 ↦ volume.restrict (Ioo (0 : ℝ) 1)) ![f, g]
  simpa [Fin.prod_univ_two, independenceCopula] using h

/-- Functions bounded on the open unit square are integrable against the independence copula. -/
lemma integrable_independenceCopula_two {h : (Fin 2 → ℝ) → ℝ} (hm : Measurable h) (M : ℝ)
    (hM : ∀ v : Fin 2 → ℝ, (∀ i, v i ∈ Ioo 0 1) → |h v| ≤ M) :
    Integrable h (independenceCopula (Fin 2)) := by
  have := isCopula_independenceCopula (ι := Fin 2) |>.isProbabilityMeasure
  refine Integrable.of_bound hm.aestronglyMeasurable M ?_
  filter_upwards [isCopula_independenceCopula.ae_mem_Ioo] with v hv
  exact hM v hv

/-- The FGM density restricted to a rectangle splits into two products of one-coordinate
functions. -/
private lemma indicator_rect_fgmDensity (θ : ℝ) (A B : Set ℝ) :
    {v : Fin 2 → ℝ | v 0 ∈ A ∧ v 1 ∈ B}.indicator (fgmDensity θ) = fun v ↦
      A.indicator 1 (v 0) * B.indicator 1 (v 1) +
        θ * (A.indicator (fun x ↦ 1 - 2 * x) (v 0) * B.indicator (fun y ↦ 1 - 2 * y) (v 1)) := by
  ext v
  by_cases h0 : v 0 ∈ A <;> by_cases h1 : v 1 ∈ B <;>
    simp [h0, h1, indicator_of_mem, indicator_of_notMem, fgmDensity]

/-- **Mass of a rectangle** under the FGM copula. For measurable `A`, `B`, with `λ` the uniform
law on `(0, 1)`, the FGM mass of `{U₀ ∈ A, U₁ ∈ B}` is
`λ(A) λ(B) + θ (∫_A (1 − 2x) dλ) (∫_B (1 − 2y) dλ)`. -/
theorem fgmCopula_rect (hθ : |θ| ≤ 1) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    fgmCopula θ {v | v 0 ∈ A ∧ v 1 ∈ B} = ENNReal.ofReal
      ((volume.restrict (Ioo 0 1)).real A * (volume.restrict (Ioo 0 1)).real B +
        θ * ((∫ x in A, (1 - 2 * x) ∂(volume.restrict (Ioo 0 1))) *
          ∫ y in B, (1 - 2 * y) ∂(volume.restrict (Ioo 0 1)))) := by
  set S : Set (Fin 2 → ℝ) := {v | v 0 ∈ A ∧ v 1 ∈ B}
  have hS : MeasurableSet S :=
    (measurable_pi_apply 0 hA).inter (measurable_pi_apply 1 hB)
  have hint1 : Integrable (fun v : Fin 2 → ℝ ↦ A.indicator 1 (v 0) * B.indicator 1 (v 1))
      (independenceCopula (Fin 2)) :=
    integrable_independenceCopula_two
      (((measurable_const.indicator hA).comp (measurable_pi_apply 0)).mul
        ((measurable_const.indicator hB).comp (measurable_pi_apply 1))) 1 fun v _ ↦ by
      by_cases h0 : v 0 ∈ A <;> by_cases h1 : v 1 ∈ B <;> simp [h0, h1]
  have hint2 : Integrable (fun v : Fin 2 → ℝ ↦
      A.indicator (fun x ↦ 1 - 2 * x) (v 0) * B.indicator (fun y ↦ 1 - 2 * y) (v 1))
      (independenceCopula (Fin 2)) := by
    refine integrable_independenceCopula_two
      ((((measurable_const.sub (measurable_const.mul measurable_id)).indicator hA).comp
        (measurable_pi_apply 0)).mul
        (((measurable_const.sub (measurable_const.mul measurable_id)).indicator hB).comp
          (measurable_pi_apply 1))) 1 fun v hv ↦ ?_
    have hb (i : Fin 2) : |1 - 2 * v i| ≤ 1 :=
      abs_le.2 ⟨by linarith [(hv i).2], by linarith [(hv i).1]⟩
    rw [abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) ?_).trans ?_
    · by_cases h0 : v 0 ∈ A
      · simpa [h0] using hb 0
      · simp [h0]
    · by_cases h1 : v 1 ∈ B
      · simpa [h1] using hb 1
      · simp [h1]
  have hnn : 0 ≤ᵐ[independenceCopula (Fin 2)] S.indicator (fgmDensity θ) := by
    filter_upwards [isCopula_independenceCopula.ae_mem_Ioo] with v hv
    exact indicator_nonneg (fun w _ ↦ fgmDensity_nonneg hθ hv) v
  have hSint : Integrable (S.indicator (fgmDensity θ)) (independenceCopula (Fin 2)) := by
    rw [indicator_rect_fgmDensity]; exact hint1.add (hint2.const_mul θ)
  rw [fgmCopula, withDensity_apply _ hS, ← lintegral_indicator hS,
    show S.indicator (fun v ↦ ENNReal.ofReal (fgmDensity θ v)) =
      fun v ↦ ENNReal.ofReal (S.indicator (fgmDensity θ) v) by
        ext v; by_cases hv : v ∈ S <;> simp [hv],
    ← ofReal_integral_eq_lintegral_ofReal hSint hnn, indicator_rect_fgmDensity,
    integral_add hint1 (hint2.const_mul θ), integral_const_mul, integral_independenceCopula_two,
    integral_independenceCopula_two, integral_indicator_one hA, integral_indicator_one hB,
    integral_indicator hA, integral_indicator hB]

/-- `∫₀¹ (1 − 2x) dx = 0`: the FGM perturbation integrates out of each margin. -/
lemma integral_uniformIoo_one_sub_two_mul :
    ∫ x, (1 - 2 * x) ∂(volume.restrict (Ioo (0 : ℝ) 1)) = 0 := by
  rw [integral_uniformIoo, intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun x : ℝ ↦ 2 * x).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_id]
  norm_num

/-- `∫₀ᵗ (1 − 2x) dx = t − t²`. -/
lemma integral_zero_one_sub_two_mul (t : ℝ) : ∫ x in (0 : ℝ)..t, (1 - 2 * x) = t - t ^ 2 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun x : ℝ ↦ 2 * x).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_id]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  ring

/-- **The FGM copula is a copula** for `|θ| ≤ 1`. -/
theorem isCopula_fgmCopula (hθ : |θ| ≤ 1) : IsCopula (fgmCopula θ) := by
  have hmarg (A : Set ℝ) (hA : MeasurableSet A) (i : Fin 2) :
      fgmCopula θ ((fun v : Fin 2 → ℝ ↦ v i) ⁻¹' A) = volume.restrict (Ioo 0 1) A := by
    have hint : ∫ y in univ, (1 - 2 * y) ∂(volume.restrict (Ioo (0 : ℝ) 1)) = 0 := by
      rw [Measure.restrict_univ, integral_uniformIoo_one_sub_two_mul]
    fin_cases i
    · change fgmCopula θ ((fun v : Fin 2 → ℝ ↦ v 0) ⁻¹' A) = _
      rw [show (fun v : Fin 2 → ℝ ↦ v 0) ⁻¹' A = {v | v 0 ∈ A ∧ v 1 ∈ univ} by ext; simp,
        fgmCopula_rect hθ hA MeasurableSet.univ, probReal_univ, hint, mul_one, mul_zero,
        mul_zero, add_zero, ofReal_measureReal]
    · change fgmCopula θ ((fun v : Fin 2 → ℝ ↦ v 1) ⁻¹' A) = _
      rw [show (fun v : Fin 2 → ℝ ↦ v 1) ⁻¹' A = {v | v 0 ∈ univ ∧ v 1 ∈ A} by ext; simp,
        fgmCopula_rect hθ MeasurableSet.univ hA, probReal_univ, hint, one_mul, zero_mul,
        mul_zero, add_zero, ofReal_measureReal]
  have hprob : IsProbabilityMeasure (fgmCopula θ) :=
    ⟨by simpa using hmarg univ MeasurableSet.univ 0⟩
  exact ⟨hprob, fun i ↦ Measure.ext fun A hA ↦ by
    rw [Measure.map_apply (measurable_pi_apply i) hA, hmarg A hA i]⟩

/-- **The FGM distribution function**: `C(u) = u₀u₁ + θ u₀u₁(1 − u₀)(1 − u₁)` on `[0, 1]²`. -/
theorem fgmCopula_real_Iic (hθ : |θ| ≤ 1) (u : Fin 2 → ℝ) (hu : ∀ i, u i ∈ Icc 0 1) :
    (fgmCopula θ).real (Iic u) = u 0 * u 1 + θ * u 0 * u 1 * (1 - u 0) * (1 - u 1) := by
  have := (isCopula_fgmCopula hθ).isProbabilityMeasure
  rw [show Iic u = {v : Fin 2 → ℝ | v 0 ∈ Iic (u 0) ∧ v 1 ∈ Iic (u 1)} by
      ext v; simp [Pi.le_def, Fin.forall_fin_two],
    measureReal_def, fgmCopula_rect hθ measurableSet_Iic measurableSet_Iic,
    uniformIoo_real_Iic (hu 0).1 (hu 0).2, uniformIoo_real_Iic (hu 1).1 (hu 1).2,
    setIntegral_uniformIoo_Iic _ (hu 0).1 (hu 0).2, setIntegral_uniformIoo_Iic _ (hu 1).1 (hu 1).2,
    integral_zero_one_sub_two_mul, integral_zero_one_sub_two_mul, ENNReal.toReal_ofReal]
  · ring
  · -- the closed form is the mass of an orthant, hence nonnegative
    have h0 := (hu 0).1; have h1 := (hu 1).1; have h0' := (hu 0).2; have h1' := (hu 1).2
    have ha : 0 ≤ u 0 - u 0 ^ 2 := by nlinarith
    have hb : 0 ≤ u 1 - u 1 ^ 2 := by nlinarith
    have hθ' := abs_le.1 hθ
    nlinarith [mul_nonneg ha hb, mul_le_mul_of_nonneg_left (sub_le_self (u 0) (sq_nonneg (u 0))) h1,
      mul_nonneg (mul_nonneg ha hb) (by linarith : (0 : ℝ) ≤ 1 + θ)]

/-- **FGM is a copula exactly for `|θ| ≤ 1`** (QRM Exercise Book, Exercise 7.19): some copula has
distribution function `uv + θ uv(1 − u)(1 − v)` on `[0, 1]²` if and only if `|θ| ≤ 1`. For
`θ < −1` the mass of a small square at the origin would be negative, and for `θ > 1` so would the
mass of a thin strip `{U₀ ≤ ε, U₁ > 1 − ε}`. -/
theorem exists_isCopula_fgm_iff (θ : ℝ) :
    (∃ C : Measure (Fin 2 → ℝ), IsCopula C ∧ ∀ u : Fin 2 → ℝ, (∀ i, u i ∈ Icc 0 1) →
      C.real (Iic u) = u 0 * u 1 + θ * u 0 * u 1 * (1 - u 0) * (1 - u 1)) ↔ |θ| ≤ 1 := by
  refine ⟨fun ⟨C, hC, hdf⟩ ↦ ?_, fun hθ ↦ ⟨fgmCopula θ, isCopula_fgmCopula hθ,
    fgmCopula_real_Iic hθ⟩⟩
  have := hC.isProbabilityMeasure
  -- for `1 + a < 0`, some level `ε ∈ (0, 1)` keeps `1 + a (1 − ε)²` negative
  have hsmall (a : ℝ) (ha : 1 + a < 0) : ∃ ε ∈ Ioo (0 : ℝ) 1, 1 + a * (1 - ε) ^ 2 < 0 := by
    have hlim : Tendsto (fun ε : ℝ ↦ 1 + a * (1 - ε) ^ 2) (𝓝[>] 0) (𝓝 (1 + a)) := by
      have hcont : Continuous fun ε : ℝ ↦ 1 + a * (1 - ε) ^ 2 := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, hε, hε01⟩ := ((hlim.eventually_lt_const ha).and (Ioo_mem_nhdsGT one_pos)).exists
    exact ⟨ε, hε01, hε⟩
  by_contra hθ
  rw [abs_le, not_and_or, not_le, not_le] at hθ
  rcases hθ with hneg | hpos
  · -- `θ < −1`: the square `[0, ε]²` would carry negative mass
    obtain ⟨ε, hε, hneg'⟩ := hsmall θ (by linarith)
    have h := hdf ![ε, ε] fun i ↦ by fin_cases i <;> exact ⟨hε.1.le, hε.2.le⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hnn := measureReal_nonneg (μ := C) (s := Iic ![ε, ε])
    rw [h] at hnn
    nlinarith [mul_pos (mul_pos hε.1 hε.1) (neg_pos.2 hneg')]
  · -- `θ > 1`: the strip `{U₀ ≤ ε, U₁ > 1 − ε}` would carry negative mass
    obtain ⟨ε, hε, hneg'⟩ := hsmall (-θ) (by linarith)
    have h := hdf ![ε, 1 - ε] fun i ↦ by
      fin_cases i <;> simp <;> constructor <;> linarith [hε.1, hε.2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hsub : C.real (Iic ![ε, 1 - ε]) ≤ C.real {v : Fin 2 → ℝ | v 0 ≤ ε} :=
      measureReal_mono fun v hv ↦ by simpa using hv 0
    rw [h, hC.measureReal_coord_le 0 hε.1.le hε.2.le] at hsub
    nlinarith [mul_pos (mul_pos hε.1 hε.1) (neg_pos.2 hneg')]

/-- **Spearman's rho of the FGM copula is `θ/3`** (QRM Exercise Book, Exercise 7.19(d)), so the
family attains rank correlations only in `[−1/3, 1/3]`. -/
theorem spearmanRho_fgmCopula (hθ : |θ| ≤ 1) : spearmanRho (fgmCopula θ) = θ / 3 := by
  rw [(isCopula_fgmCopula hθ).spearmanRho_eq]
  have hnn : ∀ᵐ v ∂(independenceCopula (Fin 2)), 0 ≤ fgmDensity θ v := by
    filter_upwards [isCopula_independenceCopula.ae_mem_Ioo] with v hv
    exact fgmDensity_nonneg hθ hv
  have hpt : (fun v : Fin 2 → ℝ ↦ (ENNReal.ofReal (fgmDensity θ v)).toReal • (v 0 * v 1)) =ᵐ[
      independenceCopula (Fin 2)] fun v ↦ v 0 * v 1 +
        θ * ((v 0 * (1 - 2 * v 0)) * (v 1 * (1 - 2 * v 1))) := by
    filter_upwards [hnn] with v hv
    rw [ENNReal.toReal_ofReal hv, smul_eq_mul, fgmDensity]
    ring
  have hint1 : Integrable (fun v : Fin 2 → ℝ ↦ v 0 * v 1) (independenceCopula (Fin 2)) :=
    integrable_independenceCopula_two (by fun_prop) 1 fun v hv ↦ by
      rw [abs_mul, abs_of_pos (hv 0).1, abs_of_pos (hv 1).1]
      exact (mul_le_of_le_one_left (hv 1).1.le (hv 0).2.le).trans (hv 1).2.le
  have hint2 : Integrable (fun v : Fin 2 → ℝ ↦ (v 0 * (1 - 2 * v 0)) * (v 1 * (1 - 2 * v 1)))
      (independenceCopula (Fin 2)) :=
    integrable_independenceCopula_two (by fun_prop) 1 fun v hv ↦ by
      have hb (i : Fin 2) : |v i * (1 - 2 * v i)| ≤ 1 := by
        rw [abs_mul, abs_of_pos (hv i).1]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hv i).2.le).trans
          (abs_le.2 ⟨by linarith [(hv i).2], by linarith [(hv i).1]⟩)
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hb 0)).trans (hb 1)
  have hx : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by rw [integral_id]; norm_num
  have hx2 : ∫ x in (0 : ℝ)..1, x * (1 - 2 * x) = -1 / 6 := by
    rw [show (fun x : ℝ ↦ x * (1 - 2 * x)) = fun x ↦ x - 2 * x ^ 2 by ext x; ring,
      intervalIntegral.integral_sub
          ((by fun_prop : Continuous fun x : ℝ ↦ x).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun x : ℝ ↦ 2 * x ^ 2).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    norm_num
  rw [fgmCopula, integral_withDensity_eq_integral_toReal_smul
      (measurable_fgmDensity θ).ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    integral_congr_ae hpt, integral_add hint1 (hint2.const_mul θ), integral_const_mul,
    integral_independenceCopula_two (fun x ↦ x) (fun x ↦ x),
    integral_independenceCopula_two (fun x ↦ x * (1 - 2 * x)) (fun x ↦ x * (1 - 2 * x)),
    integral_uniformIoo, integral_uniformIoo, hx, hx2]
  ring

/-! ### The Clayton copula function -/

/-- The **Clayton copula function** `C_θ(u, v) = (u^{−θ} + v^{−θ} − 1)^{−1/θ}`. Only the function
is studied here. That it is the distribution function of a copula is not proved. -/
noncomputable def claytonCopulaFun (θ u v : ℝ) : ℝ :=
  (u ^ (-θ) + v ^ (-θ) - 1) ^ (-1 / θ)

/-- On the diagonal, `C_θ(u, u) = u (2 − u^θ)^{−1/θ}`. -/
lemma claytonCopulaFun_diag (hθ : 0 < θ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    claytonCopulaFun θ u u = u * (2 - u ^ θ) ^ (-1 / θ) := by
  have hpow : u ^ θ ≤ 1 := Real.rpow_le_one hu.le hu1 hθ.le
  have hsplit : u ^ (-θ) + u ^ (-θ) - 1 = u ^ (-θ) * (2 - u ^ θ) := by
    rw [mul_sub, ← Real.rpow_add hu, neg_add_cancel, Real.rpow_zero]
    ring
  rw [claytonCopulaFun, hsplit, Real.mul_rpow (Real.rpow_nonneg hu.le _) (by linarith),
    ← Real.rpow_mul hu.le, show -θ * (-1 / θ) = 1 by field_simp, Real.rpow_one]

/-- **Lower tail dependence of the Clayton copula** (QRM Exercise Book, Exercise 7.17(b)):
`λ_l = lim_{u → 0⁺} C_θ(u, u)/u = 2^{−1/θ}`. -/
theorem tendsto_claytonCopulaFun_diag_div (hθ : 0 < θ) :
    Tendsto (fun u ↦ claytonCopulaFun θ u u / u) (𝓝[>] 0) (𝓝 (2 ^ (-1 / θ))) := by
  have hpow : Tendsto (fun u : ℝ ↦ u ^ θ) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [Real.zero_rpow hθ.ne'] using this
  have hlim : Tendsto (fun u : ℝ ↦ (2 - u ^ θ) ^ (-1 / θ)) (𝓝[>] 0) (𝓝 (2 ^ (-1 / θ))) := by
    have h2 : Tendsto (fun u : ℝ ↦ 2 - u ^ θ) (𝓝[>] 0) (𝓝 2) := by
      simpa using (tendsto_const_nhds (x := (2 : ℝ))).sub hpow
    exact (Real.continuousAt_rpow_const 2 (-1 / θ) (Or.inl two_ne_zero)).tendsto.comp h2
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with u hu
  rw [claytonCopulaFun_diag hθ hu.1 hu.2.le, mul_div_cancel_left₀ _ hu.1.ne']

/-- **The Clayton copula tends to the comonotonicity copula as `θ → ∞`** (QRM Exercise Book,
Exercise 7.17(d)): `C_θ(u, v) → min(u, v)` for `u, v ∈ (0, 1]`. -/
theorem tendsto_claytonCopulaFun_atTop {u v : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hv : 0 < v)
    (hv1 : v ≤ 1) : Tendsto (fun θ ↦ claytonCopulaFun θ u v) atTop (𝓝 (min u v)) := by
  have hm : 0 < min u v := lt_min hu hv
  -- `m^{−θ} ≤ u^{−θ} + v^{−θ} − 1 ≤ 2 m^{−θ}` for `θ > 0`, with `m = min u v`
  have hlo (θ : ℝ) (hθ : 0 < θ) : min u v ^ (-θ) ≤ u ^ (-θ) + v ^ (-θ) - 1 := by
    have hu' : 1 ≤ u ^ (-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1 (by linarith)
    have hv' : 1 ≤ v ^ (-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv hv1 (by linarith)
    rcases min_choice u v with h | h <;> rw [h] <;> linarith
  have hhi (θ : ℝ) (hθ : 0 < θ) : u ^ (-θ) + v ^ (-θ) - 1 ≤ 2 * min u v ^ (-θ) := by
    have hu' : u ^ (-θ) ≤ min u v ^ (-θ) :=
      Real.rpow_le_rpow_of_nonpos hm (min_le_left u v) (by linarith)
    have hv' : v ^ (-θ) ≤ min u v ^ (-θ) :=
      Real.rpow_le_rpow_of_nonpos hm (min_le_right u v) (by linarith)
    have hv1' : 1 ≤ v ^ (-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv hv1 (by linarith)
    linarith
  have hexp (θ : ℝ) (hθ : 0 < θ) : -1 / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hθ.le
  have hmθ (θ : ℝ) (hθ : 0 < θ) : (min u v ^ (-θ)) ^ (-1 / θ) = min u v := by
    rw [← Real.rpow_mul hm.le, show -θ * (-1 / θ) = 1 by field_simp, Real.rpow_one]
  have hup (θ : ℝ) (hθ : 0 < θ) : claytonCopulaFun θ u v ≤ min u v := by
    rw [claytonCopulaFun, ← hmθ θ hθ]
    exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hm _) (hlo θ hθ) (hexp θ hθ)
  have hdown (θ : ℝ) (hθ : 0 < θ) : (2 : ℝ) ^ (-1 / θ) * min u v ≤ claytonCopulaFun θ u v := by
    rw [claytonCopulaFun, ← hmθ θ hθ, ← Real.mul_rpow zero_le_two (Real.rpow_nonneg hm.le _)]
    exact Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le (Real.rpow_pos_of_pos hm _) (hlo θ hθ)) (hhi θ hθ) (hexp θ hθ)
  have hlim2 : Tendsto (fun θ : ℝ ↦ (2 : ℝ) ^ (-1 / θ) * min u v) atTop (𝓝 (min u v)) := by
    have h0 : Tendsto (fun θ : ℝ ↦ -1 / θ) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := ((Real.continuousAt_const_rpow two_ne_zero (b := 0)).tendsto.comp h0).mul_const
      (min u v)
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim2 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with θ hθ using hdown θ hθ
  · filter_upwards [eventually_gt_atTop 0] with θ hθ using hup θ hθ

/-- **The Clayton copula tends to the independence copula as `θ → 0⁺`** (QRM Exercise Book,
Exercise 7.17(c)): `C_θ(u, v) → uv` for `u, v ∈ (0, 1]`. Writing
`C_θ = exp(−θ⁻¹ log(u^{−θ} + v^{−θ} − 1))`, the exponent is minus the difference quotient at `0`
of `θ ↦ log(u^{−θ} + v^{−θ} − 1)`, whose derivative there is `−log u − log v`. -/
theorem tendsto_claytonCopulaFun_zero {u v : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hv : 0 < v)
    (hv1 : v ≤ 1) : Tendsto (fun θ ↦ claytonCopulaFun θ u v) (𝓝[>] 0) (𝓝 (u * v)) := by
  set s : ℝ → ℝ := fun θ ↦ u ^ (-θ) + v ^ (-θ) - 1
  have hs0 : s 0 = 1 := by simp [s]
  have hspos (θ : ℝ) (hθ : 0 < θ) : 0 < s θ := by
    have hu' : 1 ≤ u ^ (-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1 (by linarith)
    have hv' : 1 ≤ v ^ (-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv hv1 (by linarith)
    simp only [s]; linarith
  have hpow (x : ℝ) (hx : 0 < x) : HasDerivAt (fun θ : ℝ ↦ x ^ (-θ)) (-Real.log x) 0 := by
    have h := (Real.hasStrictDerivAt_const_rpow hx (-0)).hasDerivAt.comp 0 (hasDerivAt_neg 0)
    rw [neg_zero, Real.rpow_zero, one_mul, mul_neg_one] at h
    exact h
  have hderiv : HasDerivAt (fun θ ↦ Real.log (s θ)) (-Real.log u + -Real.log v) 0 := by
    have hs : HasDerivAt s (-Real.log u + -Real.log v) 0 :=
      ((hpow u hu).add (hpow v hv)).sub_const 1
    have h := hs.log (by rw [hs0]; exact one_ne_zero)
    rwa [hs0, div_one] at h
  have hslope : Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log (s t)) (𝓝[>] 0)
      (𝓝 (-Real.log u + -Real.log v)) := by
    simpa [hs0] using hderiv.tendsto_slope_zero_right
  have hexp : Tendsto (fun θ : ℝ ↦ Real.exp (-(θ⁻¹ * Real.log (s θ)))) (𝓝[>] 0)
      (𝓝 (Real.exp (-(-Real.log u + -Real.log v)))) :=
    (Real.continuous_exp.tendsto _).comp hslope.neg
  rw [show -(-Real.log u + -Real.log v) = Real.log (u * v) by
      rw [Real.log_mul hu.ne' hv.ne']; ring, Real.exp_log (mul_pos hu hv)] at hexp
  refine hexp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  rw [claytonCopulaFun, Real.rpow_def_of_pos (hspos θ hθ)]
  congr 1
  ring

end MathFin

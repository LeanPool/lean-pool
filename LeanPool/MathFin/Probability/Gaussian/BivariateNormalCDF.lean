/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.NormalQuantile
public import LeanPool.MathFin.Probability.Gaussian.BivariateGaussian
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The standard bivariate normal CDF `N₂(a, b; r)`

For independent standard normals `Z₁, Z₂` (the coordinates of `N(0,1) ⊗ N(0,1)`) and
`r ∈ [-1, 1]`, the Cholesky construction

    X = r Z₂ + √(1 − r²) Z₁,   Y = Z₂

gives a standard bivariate normal pair with correlation `r`, and
`N₂(a, b; r) = P(X ≤ a, Y ≤ b)`.

The Cholesky map is a continuous linear map, so `bivariateNormalLaw r` is Gaussian in Mathlib's
sense (`IsGaussian`, via `isGaussian_map` and Mathlib's instance for products of Gaussian
measures). A Gaussian measure is determined by its mean and covariance (Mathlib's
characteristic-function `Measure.ext_of_charFunDual` with `IsGaussian.charFunDual_eq'`); on `ℝ²`
this says that a centred Gaussian law with unit variances and covariance `r` is
`bivariateNormalLaw r` (`eq_bivariateNormalLaw`). The swap symmetry is derived from it.

## Main definitions

* `stdNormalPair`: the law `N(0,1) ⊗ N(0,1)` of two independent standard normals on `ℝ × ℝ`.
* `stdNormalVec`: the law of a vector of independent standard normals indexed by a finite type.
* `choleskyPair`: the continuous linear map `(z₁, z₂) ↦ (r z₂ + √(1 − r²) z₁, z₂)`.
* `bivariateNormalLaw`: the law of the Cholesky pair; for `r² ≤ 1` the standard bivariate normal
  law with correlation `r`.
* `bivariateNormalCDF`: `N₂(a, b; r) = P(X ≤ a, Y ≤ b)` for the Cholesky pair `(X, Y)`.
* `gaussianPair`: the Cholesky pair shifted and scaled, coordinate `i` being `μᵢ + σᵢ Zᵢ`.

## Main results

* `stdNormalPair`, `map_linear_stdNormalPair`: `c Z₁ + d Z₂ ∼ N(0, c² + d²)`.
* `stdNormalVec ι`: the law `N(0, 1)^ι` of a vector of independent standard normals, and its
  `IsGaussian` instance (Mathlib's `iIndepFun.hasGaussianLaw`). Pushed to
  `EuclideanSpace ℝ ι` it is Mathlib's `stdGaussian` (`map_pi_eq_stdGaussian`).
* `isGaussian_bivariateNormalLaw`: the law of the Cholesky pair is Gaussian, for every `r`.
* `covariance_fst_snd_bivariateNormalLaw`, `variance_snd_bivariateNormalLaw`: `Cov(X, Y) = r` and
  `Var Y = 1` for every `r`; `variance_fst_bivariateNormalLaw`: `Var X = 1` for `r² ≤ 1`.
* `map_fst_bivariateNormalLaw`, `map_snd_bivariateNormalLaw`: both margins are `N(0, 1)`, read
  off Mathlib's `IsGaussian.map_eq_gaussianReal`.
* `eq_bivariateNormalLaw`: a Gaussian law on `ℝ²` with centred coordinates, unit variances and
  covariance `r` (`r² ≤ 1`) is `bivariateNormalLaw r`.
* `gaussianPair`, `hasGaussianLaw_gaussianPair`, `integral_gaussianPair`,
  `variance_gaussianPair`, `covariance_gaussianPair`: `(μ₀ + σ₀ X, μ₁ + σ₁ Y)` is a Gaussian pair
  with means `μ`, variances `σ²` and covariance `r σ₀ σ₁` (`r² ≤ 1` for the variances), so every
  two-asset Gaussian model has a realization.
* `bivariateGaussianHyp_bivariateNormalLaw`, `condExp_fst_bivariateNormalLaw`: the pair satisfies
  the hypotheses `BivariateGaussianHyp` of `Probability/Gaussian/BivariateGaussian.lean`, so
  `E[X | Y] = r Y` almost surely.
* `bivariateNormalLaw_map_swap`, `bivariateNormalCDF_comm`: `(Y, X)` has the same law as
  `(X, Y)`, so `N₂(a, b; r) = N₂(b, a; r)`.
* `bivariateNormalCDF_zero`, `bivariateNormalCDF_one`, `bivariateNormalCDF_neg_one`: the
  independent, comonotone and countermonotone cases; `posPart_Phi_sub_Phi`:
  `(Φ(t) − Φ(k))⁺` is the standard normal probability of `(k, t]`.
* `bivariateNormalCDF_flip_snd`: **`N₂(a, b; r) + N₂(a, -b; -r) = Φ(a)`**, the two-asset
  analogue of `Phi_add_Phi_neg` — the key algebraic ingredient behind exact two-asset closed
  forms (Stulz 1982, Heynen & Kat 1994/96) that package `N₂(·,·;ρ)` / `N₂(·,·;-ρ)` pairs.
* `bivariateNormalCDF_neg_neg`: **`N₂(-a, -b; r) = 1 - Φ(a) - Φ(b) + N₂(a, b; r)`**, the joint
  survival identity, derived purely algebraically from `bivariateNormalCDF_flip_snd`,
  `bivariateNormalCDF_comm` and `Phi_neg` (no new measure-theoretic argument). Reading either
  side as the joint survival `P(X > a, Y > b)` is not stated here.

Outside `r ∈ [-1, 1]` the square root truncates to `0` and the construction is no longer the
standard bivariate normal with correlation `r` (it degenerates to the law of `(rY, Y)`, still with
`Cov(X, Y) = r` but `Var X = r²`); every result that needs unit variances carries the hypothesis
`r ^ 2 ≤ 1`.

Mathlib's `ProbabilityTheory.multivariateGaussian` lives on `EuclideanSpace ℝ (Fin 2)` rather
than `ℝ × ℝ`; the identification of `bivariateNormalLaw r` with it is not stated here.

## References

* [P. Billingsley, *Probability and Measure*][Billingsley1995], §29

## Tags

bivariate normal distribution, Cholesky construction, correlation, Gaussian vector,
two-asset option, joint distribution function, MSC 60E05, MSC 60G15, JEL C02
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set

/-- The law of two independent standard normals, `N(0,1) ⊗ N(0,1)`. It is Gaussian by Mathlib's
instance for products of Gaussian measures. -/
noncomputable abbrev stdNormalPair : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- The law of a vector of independent standard normals indexed by `ι`: Mathlib's product measure
`Measure.pi` of `N(0, 1)`. Its image under `WithLp.toLp 2` is Mathlib's
`stdGaussian (EuclideanSpace ℝ ι)` (`map_pi_eq_stdGaussian`). -/
noncomputable abbrev stdNormalVec (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι ↦ gaussianReal 0 1

/-- **A vector of independent standard normals is Gaussian**: Mathlib's
`iIndepFun.hasGaussianLaw` applied to the coordinates of `Measure.pi`. -/
instance isGaussian_stdNormalVec (ι : Type*) [Fintype ι] : IsGaussian (stdNormalVec ι) := by
  have h : HasGaussianLaw id (stdNormalVec ι) :=
    iIndepFun.hasGaussianLaw (X := fun i (x : ι → ℝ) ↦ x i)
      (fun i ↦ (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).hasLaw.hasGaussianLaw)
      (iIndepFun_pi (X := fun _ : ι ↦ id) fun _ ↦ aemeasurable_id)
  simpa using h.isGaussian_map

/-- A coordinate of a vector of independent standard normals is square integrable. -/
lemma memLp_eval_stdNormalVec {ι : Type*} [Fintype ι] (i : ι) :
    MemLp (fun w : ι → ℝ ↦ w i) 2 (stdNormalVec ι) :=
  (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).hasLaw.memLp (memLp_id_gaussianReal 2)

/-- The Cholesky map `(z₁, z₂) ↦ (r z₂ + √(1 − r²) z₁, z₂)`, as a continuous linear map. -/
noncomputable def choleskyPair (r : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (r • ContinuousLinearMap.snd ℝ ℝ ℝ + √(1 - r ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp]
lemma choleskyPair_apply (r : ℝ) (p : ℝ × ℝ) :
    choleskyPair r p = (r * p.2 + √(1 - r ^ 2) * p.1, p.2) := by
  simp [choleskyPair]

@[fun_prop]
lemma measurable_choleskyPair (r : ℝ) : Measurable (choleskyPair r) :=
  (choleskyPair r).measurable

/-- The law of the Cholesky pair. For `r ^ 2 ≤ 1` it is the standard bivariate normal law with
correlation `r` (`eq_bivariateNormalLaw`, `map_fst_bivariateNormalLaw`,
`covariance_fst_snd_bivariateNormalLaw`); for `r ^ 2 > 1` it is the law of `(rY, Y)`. -/
noncomputable def bivariateNormalLaw (r : ℝ) : Measure (ℝ × ℝ) :=
  stdNormalPair.map (choleskyPair r)

instance (r : ℝ) : IsProbabilityMeasure (bivariateNormalLaw r) :=
  inferInstanceAs (IsProbabilityMeasure (stdNormalPair.map (choleskyPair r)))

/-- **The Cholesky pair is Gaussian**, for every `r`: the image of the Gaussian measure
`N(0,1) ⊗ N(0,1)` under a continuous linear map (Mathlib's `isGaussian_map`). -/
instance isGaussian_bivariateNormalLaw (r : ℝ) : IsGaussian (bivariateNormalLaw r) :=
  inferInstanceAs (IsGaussian (stdNormalPair.map (choleskyPair r)))

/-- **The standard bivariate normal CDF** `N₂(a, b; r) = P(X ≤ a, Y ≤ b)` for the Cholesky pair
`X = r Z₂ + √(1 − r²) Z₁`, `Y = Z₂`. -/
noncomputable def bivariateNormalCDF (a b r : ℝ) : ℝ :=
  stdNormalPair.real {p : ℝ × ℝ | r * p.2 + √(1 - r ^ 2) * p.1 ≤ a ∧ p.2 ≤ b}

/-- `N₂(a, b; r)` is the `bivariateNormalLaw r`-measure of the quadrant `(-∞, a] × (-∞, b]`. -/
lemma bivariateNormalCDF_eq_law (a b r : ℝ) :
    bivariateNormalCDF a b r = (bivariateNormalLaw r).real (Iic a ×ˢ Iic b) := by
  rw [bivariateNormalCDF, bivariateNormalLaw, map_measureReal_apply (measurable_choleskyPair r)
    (measurableSet_Iic.prod measurableSet_Iic)]
  congr 1

/-- A linear combination of independent standard normals: `c Z₁ + d Z₂ ∼ N(0, c² + d²)`. -/
lemma map_linear_stdNormalPair (c d : ℝ) :
    stdNormalPair.map (fun p ↦ c * p.1 + d * p.2) =
      gaussianReal 0 (c ^ 2 + d ^ 2).toNNReal := by
  have hf : (fun p : ℝ × ℝ ↦ c * p.1 + d * p.2) =
      (fun q : ℝ × ℝ ↦ q.1 + q.2) ∘ Prod.map (c * ·) (d * ·) := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_prod_map _ _
    (by fun_prop) (by fun_prop), gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  change gaussianReal _ _ ∗ gaussianReal _ _ = _
  rw [gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · ext; rw [Real.coe_toNNReal _ (by positivity)]; simp

/-- A linear functional of the Cholesky pair, for every `r`:
`c X + d Y ∼ N(0, (c √(1 − r²))² + (c r + d)²)`. -/
lemma map_linear_bivariateNormalLaw' (r c d : ℝ) :
    (bivariateNormalLaw r).map (fun q ↦ c * q.1 + d * q.2) =
      gaussianReal 0 ((c * √(1 - r ^ 2)) ^ 2 + (c * r + d) ^ 2).toNNReal := by
  rw [bivariateNormalLaw, Measure.map_map (by fun_prop) (measurable_choleskyPair r)]
  have hf : (fun q : ℝ × ℝ ↦ c * q.1 + d * q.2) ∘ choleskyPair r =
      fun p ↦ (c * √(1 - r ^ 2)) * p.1 + (c * r + d) * p.2 := by
    ext p; simp only [Function.comp, choleskyPair_apply]; ring
  rw [hf, map_linear_stdNormalPair]

/-- A linear functional of the bivariate normal pair: `c X + d Y ∼ N(0, c² + 2cdr + d²)`. -/
lemma map_linear_bivariateNormalLaw {r : ℝ} (hr : r ^ 2 ≤ 1) (c d : ℝ) :
    (bivariateNormalLaw r).map (fun q ↦ c * q.1 + d * q.2) =
      gaussianReal 0 (c ^ 2 + 2 * c * d * r + d ^ 2).toNNReal := by
  rw [map_linear_bivariateNormalLaw', mul_pow, sq_sqrt (by linarith)]
  congr 2
  ring

/-- `c X + d Y ∈ L²(bivariateNormalLaw r)`, for every `r`. -/
lemma memLp_linear_bivariateNormalLaw (r c d : ℝ) :
    MemLp (fun q : ℝ × ℝ ↦ c * q.1 + d * q.2) 2 (bivariateNormalLaw r) :=
  HasLaw.memLp ⟨by fun_prop, map_linear_bivariateNormalLaw' r c d⟩ (memLp_id_gaussianReal 2)

lemma memLp_fst_bivariateNormalLaw (r : ℝ) : MemLp Prod.fst 2 (bivariateNormalLaw r) := by
  simpa using memLp_linear_bivariateNormalLaw r 1 0

lemma memLp_snd_bivariateNormalLaw (r : ℝ) : MemLp Prod.snd 2 (bivariateNormalLaw r) := by
  simpa using memLp_linear_bivariateNormalLaw r 0 1

/-- `E[c X + d Y] = 0`, for every `r`. -/
lemma integral_linear_bivariateNormalLaw (r c d : ℝ) :
    ∫ q, c * q.1 + d * q.2 ∂bivariateNormalLaw r = 0 := by
  have h := integral_id_gaussianReal (μ := 0)
    (v := ((c * √(1 - r ^ 2)) ^ 2 + (c * r + d) ^ 2).toNNReal)
  rw [← map_linear_bivariateNormalLaw' r c d, integral_map (by fun_prop) (by fun_prop)] at h
  exact h

lemma integral_fst_bivariateNormalLaw (r : ℝ) : ∫ q, q.1 ∂bivariateNormalLaw r = 0 := by
  simpa using integral_linear_bivariateNormalLaw r 1 0

lemma integral_snd_bivariateNormalLaw (r : ℝ) : ∫ q, q.2 ∂bivariateNormalLaw r = 0 := by
  simpa using integral_linear_bivariateNormalLaw r 0 1

/-- `Var[c X + d Y] = (c √(1 − r²))² + (c r + d)²`, for every `r`. -/
private lemma variance_linear_bivariateNormalLaw' (r c d : ℝ) :
    Var[fun q ↦ c * q.1 + d * q.2; bivariateNormalLaw r] =
      (c * √(1 - r ^ 2)) ^ 2 + (c * r + d) ^ 2 := by
  rw [← variance_id_map (by fun_prop), map_linear_bivariateNormalLaw' r c d,
    variance_id_gaussianReal, Real.coe_toNNReal _ (by positivity)]

/-- `Var[c X + d Y] = c ^ 2 + 2 c d r + d ^ 2` for `r² ≤ 1`. -/
lemma variance_linear_bivariateNormalLaw {r : ℝ} (hr : r ^ 2 ≤ 1) (c d : ℝ) :
    Var[fun q ↦ c * q.1 + d * q.2; bivariateNormalLaw r] = c ^ 2 + 2 * c * d * r + d ^ 2 := by
  rw [variance_linear_bivariateNormalLaw', mul_pow, sq_sqrt (by linarith)]
  ring

/-- `Var Y = 1`, for every `r` (`Y = Z₂` never involves the root). -/
lemma variance_snd_bivariateNormalLaw (r : ℝ) : Var[Prod.snd; bivariateNormalLaw r] = 1 := by
  rw [show (Prod.snd : ℝ × ℝ → ℝ) = fun q ↦ 0 * q.1 + 1 * q.2 by ext; simp,
    variance_linear_bivariateNormalLaw']
  ring

/-- `Var X = 1` for `r² ≤ 1` (for `r² > 1`, `X = rY` and `Var X = r²`). -/
lemma variance_fst_bivariateNormalLaw {r : ℝ} (hr : r ^ 2 ≤ 1) :
    Var[Prod.fst; bivariateNormalLaw r] = 1 := by
  rw [show (Prod.fst : ℝ × ℝ → ℝ) = fun q ↦ 1 * q.1 + 0 * q.2 by ext; simp,
    variance_linear_bivariateNormalLaw hr]
  ring

/-- **The parameter is the covariance**: `Cov(X, Y) = r`, for every `r` (for `r² > 1` the pair is
`(rY, Y)`, whose covariance is still `r`). With `variance_fst_bivariateNormalLaw` and
`variance_snd_bivariateNormalLaw`, `r` is the correlation when `r² ≤ 1`. -/
theorem covariance_fst_snd_bivariateNormalLaw (r : ℝ) :
    cov[Prod.fst, Prod.snd; bivariateNormalLaw r] = r := by
  have v₁ : Var[Prod.fst; bivariateNormalLaw r] = √(1 - r ^ 2) ^ 2 + r ^ 2 := by
    rw [show (Prod.fst : ℝ × ℝ → ℝ) = fun q ↦ 1 * q.1 + 0 * q.2 by ext; simp,
      variance_linear_bivariateNormalLaw']
    ring
  have v₃ : Var[Prod.fst + Prod.snd; bivariateNormalLaw r] = √(1 - r ^ 2) ^ 2 + (r + 1) ^ 2 := by
    rw [show (Prod.fst + Prod.snd : ℝ × ℝ → ℝ) = fun q ↦ 1 * q.1 + 1 * q.2 by ext; simp,
      variance_linear_bivariateNormalLaw']
    ring
  have hadd := variance_add (memLp_fst_bivariateNormalLaw r) (memLp_snd_bivariateNormalLaw r)
  rw [v₁, v₃, variance_snd_bivariateNormalLaw] at hadd
  linear_combination (-1 / 2 : ℝ) * hadd

/-- The first margin `X ∼ N(0, 1)`, read off Mathlib's `IsGaussian.map_eq_gaussianReal` (needs
`r ^ 2 ≤ 1`: for `|r| > 1` the junk-valued root makes `X = r Y`, which is not `N(0, 1)`). -/
lemma map_fst_bivariateNormalLaw {r : ℝ} (hr : r ^ 2 ≤ 1) :
    (bivariateNormalLaw r).map Prod.fst = gaussianReal 0 1 := by
  have h := IsGaussian.map_eq_gaussianReal (μ := bivariateNormalLaw r)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)
  simp only [ContinuousLinearMap.coe_fst'] at h
  rw [h, integral_fst_bivariateNormalLaw, variance_fst_bivariateNormalLaw hr, Real.toNNReal_one]

/-- The second margin `Y = Z₂ ∼ N(0, 1)`, for every `r`, read off Mathlib's
`IsGaussian.map_eq_gaussianReal`. -/
lemma map_snd_bivariateNormalLaw (r : ℝ) :
    (bivariateNormalLaw r).map Prod.snd = gaussianReal 0 1 := by
  have h := IsGaussian.map_eq_gaussianReal (μ := bivariateNormalLaw r)
    (ContinuousLinearMap.snd ℝ ℝ ℝ)
  simp only [ContinuousLinearMap.coe_snd'] at h
  rw [h, integral_snd_bivariateNormalLaw, variance_snd_bivariateNormalLaw, Real.toNNReal_one]

/-! ### A Gaussian law on `ℝ²` is determined by its first two moments -/

/-- `L q = L(1, 0) q₁ + L(0, 1) q₂` for a continuous linear functional on `ℝ²`. -/
lemma strongDual_prod_apply (L : StrongDual ℝ (ℝ × ℝ)) (q : ℝ × ℝ) :
    L q = L (1, 0) * q.1 + L (0, 1) * q.2 := by
  have : q = q.1 • ((1 : ℝ), (0 : ℝ)) + q.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [this]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

/-- The mean of a law on `ℝ²` with integrable coordinates is the pair of coordinate means. -/
lemma integral_id_prod_eq {μ : Measure (ℝ × ℝ)} (h₁ : Integrable Prod.fst μ)
    (h₂ : Integrable Prod.snd μ) : μ[id] = (∫ q, q.1 ∂μ, ∫ q, q.2 ∂μ) :=
  integral_pair h₁ h₂

/-- The variance of `a X + b Y` from the second moments of the coordinates. -/
lemma variance_linear_of_memLp {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (h₁ : MemLp Prod.fst 2 μ) (h₂ : MemLp Prod.snd 2 μ) (a b : ℝ) :
    Var[fun q ↦ a * q.1 + b * q.2; μ] = a ^ 2 * Var[Prod.fst; μ]
      + 2 * a * b * cov[Prod.fst, Prod.snd; μ] + b ^ 2 * Var[Prod.snd; μ] := by
  rw [variance_fun_add (h₁.const_mul a) (h₂.const_mul b), variance_const_mul, variance_const_mul,
    covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- The variance of a continuous linear functional on `ℝ²` from the second moments of the
coordinates. -/
lemma variance_strongDual {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (h₁ : MemLp Prod.fst 2 μ) (h₂ : MemLp Prod.snd 2 μ) (L : StrongDual ℝ (ℝ × ℝ)) :
    Var[L; μ] = L (1, 0) ^ 2 * Var[Prod.fst; μ]
      + 2 * L (1, 0) * L (0, 1) * cov[Prod.fst, Prod.snd; μ] + L (0, 1) ^ 2 * Var[Prod.snd; μ] := by
  set a := L (1, 0)
  set b := L (0, 1)
  have hL : ⇑L = fun q ↦ a * q.1 + b * q.2 := funext (strongDual_prod_apply L)
  rw [hL, variance_linear_of_memLp h₁ h₂]

/-- **A Gaussian law on `ℝ²` with standardized coordinates is the Cholesky law.** If `μ` is
Gaussian, its coordinates are centred with unit variances, and their covariance is `r` with
`r² ≤ 1`, then `μ = bivariateNormalLaw r`. Both laws are Gaussian with the same mean and the same
variance on every linear functional, so their characteristic functions agree (Mathlib's
`IsGaussian.charFunDual_eq'` and `Measure.ext_of_charFunDual`). -/
theorem eq_bivariateNormalLaw {μ : Measure (ℝ × ℝ)} [IsGaussian μ] {r : ℝ} (hr : r ^ 2 ≤ 1)
    (h₁ : ∫ q, q.1 ∂μ = 0) (h₂ : ∫ q, q.2 ∂μ = 0) (v₁ : Var[Prod.fst; μ] = 1)
    (v₂ : Var[Prod.snd; μ] = 1) (hc : cov[Prod.fst, Prod.snd; μ] = r) :
    μ = bivariateNormalLaw r := by
  have m₁ : MemLp Prod.fst 2 μ := by
    simpa using IsGaussian.memLp_dual μ (ContinuousLinearMap.fst ℝ ℝ ℝ) 2 (by simp)
  have m₂ : MemLp Prod.snd 2 μ := by
    simpa using IsGaussian.memLp_dual μ (ContinuousLinearMap.snd ℝ ℝ ℝ) 2 (by simp)
  have hmean : μ[id] = (bivariateNormalLaw r)[id] := by
    rw [integral_id_prod_eq (m₁.integrable one_le_two) (m₂.integrable one_le_two),
      integral_id_prod_eq ((memLp_fst_bivariateNormalLaw r).integrable one_le_two)
        ((memLp_snd_bivariateNormalLaw r).integrable one_le_two),
      h₁, h₂, integral_fst_bivariateNormalLaw, integral_snd_bivariateNormalLaw]
  refine Measure.ext_of_charFunDual (funext fun L ↦ ?_)
  rw [IsGaussian.charFunDual_eq', IsGaussian.charFunDual_eq', hmean,
    covarianceBilinDual_self_eq_variance (IsGaussian.memLp_two_id (μ := μ)),
    covarianceBilinDual_self_eq_variance (IsGaussian.memLp_two_id (μ := bivariateNormalLaw r)),
    variance_strongDual m₁ m₂, v₁, v₂, hc,
    variance_strongDual (memLp_fst_bivariateNormalLaw r) (memLp_snd_bivariateNormalLaw r),
    variance_fst_bivariateNormalLaw hr, variance_snd_bivariateNormalLaw,
    covariance_fst_snd_bivariateNormalLaw]

/-- **Exchangeability**: for `r ∈ [-1, 1]`, `(Y, X)` has the same law as `(X, Y)`. The swapped
law is Gaussian (the swap is a continuous linear equivalence) with the same moments, so
`eq_bivariateNormalLaw` applies. -/
theorem bivariateNormalLaw_map_swap {r : ℝ} (hr : r ^ 2 ≤ 1) :
    (bivariateNormalLaw r).map Prod.swap = bivariateNormalLaw r := by
  have hswap : ⇑(ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) = Prod.swap := funext fun _ ↦ by simp
  have : IsGaussian ((bivariateNormalLaw r).map Prod.swap) := by
    rw [← hswap]
    infer_instance
  refine eq_bivariateNormalLaw hr ?_ ?_ ?_ ?_ ?_
  · rw [integral_map measurable_swap.aemeasurable (by fun_prop)]
    exact integral_snd_bivariateNormalLaw r
  · rw [integral_map measurable_swap.aemeasurable (by fun_prop)]
    exact integral_fst_bivariateNormalLaw r
  · rw [variance_map (by fun_prop) measurable_swap.aemeasurable]
    exact variance_snd_bivariateNormalLaw r
  · rw [variance_map (by fun_prop) measurable_swap.aemeasurable]
    exact variance_fst_bivariateNormalLaw hr
  · rw [covariance_map_fun (by fun_prop) (by fun_prop) measurable_swap.aemeasurable]
    exact (covariance_comm _ _).trans (covariance_fst_snd_bivariateNormalLaw r)

/-- **The Cholesky pair satisfies `BivariateGaussianHyp`**
(`Probability/Gaussian/BivariateGaussian.lean`)
with means `0`, `σ_X = σ_Y = 1` and `ρ = r`, for every `r`. The structure does not constrain
`Var X`; for `r² > 1` the pair is `(rY, Y)` with `Var X = r²`, and the hypotheses still hold. -/
theorem bivariateGaussianHyp_bivariateNormalLaw (r : ℝ) :
    BivariateGaussianHyp (bivariateNormalLaw r) Prod.fst Prod.snd 0 0 1 1 r where
  σ_X_pos := one_pos
  σ_Y_pos := one_pos
  X_meas := measurable_fst
  Y_meas := measurable_snd
  joint_gaussian := IsGaussian.hasGaussianLaw_id
  mean_X := integral_fst_bivariateNormalLaw r
  mean_Y := integral_snd_bivariateNormalLaw r
  var_Y := by rw [variance_snd_bivariateNormalLaw]; norm_num
  cov_XY := by rw [covariance_fst_snd_bivariateNormalLaw]; ring

/-- **Regression of `X` on `Y`**: for the Cholesky pair, `E[X | Y] = r Y` almost surely, for every
`r`. The bivariate Gaussian conditional-expectation formula
(`BivariateGaussianHyp.conditional_expectation_formula`) at
`bivariateGaussianHyp_bivariateNormalLaw`. -/
theorem condExp_fst_bivariateNormalLaw (r : ℝ) :
    (bivariateNormalLaw r)[Prod.fst | MeasurableSpace.comap Prod.snd inferInstance]
      =ᵐ[bivariateNormalLaw r] fun p ↦ r * p.2 := by
  filter_upwards [(bivariateGaussianHyp_bivariateNormalLaw r).conditional_expectation_formula]
    with p hp
  rw [hp]
  ring

/-- **Symmetry**: `N₂(a, b; r) = N₂(b, a; r)` for `r ∈ [-1, 1]`. -/
theorem bivariateNormalCDF_comm (a b : ℝ) {r : ℝ} (hr : r ^ 2 ≤ 1) :
    bivariateNormalCDF a b r = bivariateNormalCDF b a r := by
  rw [bivariateNormalCDF_eq_law, bivariateNormalCDF_eq_law]
  conv_lhs => rw [← bivariateNormalLaw_map_swap hr]
  rw [map_measureReal_apply measurable_swap (measurableSet_Iic.prod measurableSet_Iic),
    preimage_swap_prod]

/-- `N₂(a, b; r)` in terms of `Y = Z₂` alone, when the `Z₁` coefficient vanishes. -/
private lemma bivariateNormalCDF_of_sqrt_eq_zero {a b r : ℝ} (h : √(1 - r ^ 2) = 0) :
    bivariateNormalCDF a b r = (gaussianReal 0 1).real {y | r * y ≤ a ∧ y ≤ b} := by
  have hset : {p : ℝ × ℝ | r * p.2 + √(1 - r ^ 2) * p.1 ≤ a ∧ p.2 ≤ b} =
      Prod.snd ⁻¹' {y | r * y ≤ a ∧ y ≤ b} := by ext p; simp [h]
  have hm : MeasurableSet {y : ℝ | r * y ≤ a ∧ y ≤ b} :=
    (measurableSet_le (measurable_id.const_mul r) measurable_const).inter
      (measurableSet_le measurable_id measurable_const)
  rw [bivariateNormalCDF, hset, ← map_measureReal_apply measurable_snd hm, Measure.map_snd_prod]
  simp

/-- **Independence** (`r = 0`): `N₂(a, b; 0) = Φ(a) Φ(b)`. -/
theorem bivariateNormalCDF_zero (a b : ℝ) : bivariateNormalCDF a b 0 = Phi a * Phi b := by
  have hset : {p : ℝ × ℝ | 0 * p.2 + √(1 - 0 ^ 2) * p.1 ≤ a ∧ p.2 ≤ b} = Iic a ×ˢ Iic b := by
    ext p; simp only [mem_ofPred_eq, mem_prod, mem_Iic]; norm_num
  rw [bivariateNormalCDF, hset, measureReal_prod_prod]
  rfl

/-- **Comonotone** (`r = 1`): `N₂(a, b; 1) = Φ(min a b)`. -/
theorem bivariateNormalCDF_one (a b : ℝ) : bivariateNormalCDF a b 1 = Phi (min a b) := by
  rw [bivariateNormalCDF_of_sqrt_eq_zero (by simp)]
  congr 1
  ext y; simp

/-- `(Φ(t) − Φ(k))⁺` is the standard normal probability of `(k, t]`. -/
lemma posPart_Phi_sub_Phi (k t : ℝ) :
    (Phi t - Phi k)⁺ = (gaussianReal 0 1).real (Ioc k t) := by
  rcases le_total t k with h | h
  · rw [Ioc_eq_empty (not_lt.2 h), measureReal_empty, posPart_eq_zero]
    exact sub_nonpos.2 (strictMono_Phi.monotone h)
  · rw [posPart_eq_self.2 (sub_nonneg.2 (strictMono_Phi.monotone h)), ← Iic_sdiff_Iic,
      measureReal_sdiff (Iic_subset_Iic.2 h) measurableSet_Iic, ← cdf_eq_real, ← cdf_eq_real,
      cdf_gaussianReal_zero_one]

/-- **Countermonotone** (`r = -1`): `N₂(a, b; -1) = (Φ(b) − Φ(−a))⁺`. -/
theorem bivariateNormalCDF_neg_one (a b : ℝ) :
    bivariateNormalCDF a b (-1) = (Phi b - Phi (-a))⁺ := by
  rw [bivariateNormalCDF_of_sqrt_eq_zero (by simp), posPart_Phi_sub_Phi]
  have hset : {y : ℝ | -1 * y ≤ a ∧ y ≤ b} = Icc (-a) b := by
    ext y; simp only [mem_ofPred_eq, mem_Icc]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      linarith
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  rw [hset, measureReal_congr Ioc_ae_eq_Icc.symm]

/-! ## A sign-flip identity: `N₂(a, b; r) + N₂(a, -b; -r) = Φ(a)`

Negating the second coordinate of the Cholesky pair sends correlation `r` to `-r` without
touching the `X`-margin, so splitting the real line into the closed rays `Iic b` and `Ici b`
(covering `ℝ`, meeting only at the null set `{b}` for the atom-free `Y`-margin) gives the
identity below. It is the two-asset analogue of `Phi_add_Phi_neg`. -/

/-- The sign-flip map `(x, y) ↦ (x, -y)` sends `bivariateNormalLaw r` to `bivariateNormalLaw
(-r)`: negating `Y` negates the correlation, unconditionally in `r`. -/
lemma bivariateNormalLaw_map_negSnd (r : ℝ) :
    (bivariateNormalLaw r).map (fun p : ℝ × ℝ ↦ (p.1, -p.2)) = bivariateNormalLaw (-r) := by
  have hnegStd : stdNormalPair.map (fun p : ℝ × ℝ ↦ (p.1, -p.2)) = stdNormalPair := by
    have hf : (fun p : ℝ × ℝ ↦ (p.1, -p.2)) = Prod.map id (fun x : ℝ ↦ -x) := rfl
    rw [hf, stdNormalPair, ← Measure.map_prod_map _ _ measurable_id (by fun_prop),
      Measure.map_id, gaussianReal_map_neg, neg_zero]
  have hcomm : (fun p : ℝ × ℝ ↦ (p.1, -p.2)) ∘ choleskyPair r =
      choleskyPair (-r) ∘ (fun p : ℝ × ℝ ↦ (p.1, -p.2)) := by
    funext p
    simp only [Function.comp, choleskyPair_apply, neg_sq, Prod.mk.injEq]
    constructor <;> first | ring | trivial
  rw [bivariateNormalLaw, bivariateNormalLaw,
    Measure.map_map (by fun_prop) (measurable_choleskyPair r), hcomm,
    ← Measure.map_map (measurable_choleskyPair (-r)) (by fun_prop), hnegStd]

/-- **The sign-flip identity**: `N₂(a, b; r) + N₂(a, -b; -r) = Φ(a)`. Splits `(bivariateNormalLaw
r).real (Iic a ×ˢ ·)` across the closed-ray cover `Iic b ∪ Ici b = univ` (meeting at the null
set `{b}`, since the `Y`-margin `map_snd_bivariateNormalLaw` is atom-free), then reads off the
`X`-margin via `map_fst_bivariateNormalLaw`. -/
theorem bivariateNormalCDF_flip_snd (a b : ℝ) {r : ℝ} (hr : r ^ 2 ≤ 1) :
    bivariateNormalCDF a b r + bivariateNormalCDF a (-b) (-r) = Phi a := by
  have hflip : bivariateNormalCDF a (-b) (-r) = (bivariateNormalLaw r).real (Iic a ×ˢ Ici b) := by
    rw [bivariateNormalCDF_eq_law, ← bivariateNormalLaw_map_negSnd r,
      map_measureReal_apply (by fun_prop) (measurableSet_Iic.prod measurableSet_Iic)]
    congr 1
    ext p
    simp only [mem_preimage, mem_prod, mem_Iic, mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  have hsingleton : (bivariateNormalLaw r).real (Iic a ×ˢ ({b} : Set ℝ)) = 0 := by
    have hsub : (Iic a ×ˢ ({b} : Set ℝ) : Set (ℝ × ℝ)) ⊆ univ ×ˢ ({b} : Set ℝ) :=
      prod_mono (subset_univ _) subset_rfl
    have hzero : (bivariateNormalLaw r).real (univ ×ˢ ({b} : Set ℝ)) = 0 := by
      have : NullSingletonClass (gaussianReal (0 : ℝ) (1 : NNReal)) :=
        nullSingletonClass_gaussianReal one_ne_zero
      rw [show (univ ×ˢ ({b} : Set ℝ) : Set (ℝ × ℝ)) = Prod.snd ⁻¹' {b} by ext p; simp,
        ← map_measureReal_apply measurable_snd (measurableSet_singleton b),
        map_snd_bivariateNormalLaw]
      simp [measureReal_def]
    exact le_antisymm (hzero ▸ measureReal_mono hsub) measureReal_nonneg
  have hunion : (Iic a ×ˢ Iic b : Set (ℝ × ℝ)) ∪ (Iic a ×ˢ Ici b) = Iic a ×ˢ univ := by
    rw [← prod_union]; congr 1; ext x; simp
  have hinter : (Iic a ×ˢ Iic b : Set (ℝ × ℝ)) ∩ (Iic a ×ˢ Ici b) = Iic a ×ˢ {b} := by
    rw [← prod_inter]; congr 1; ext x; simp [le_antisymm_iff]
  have hkey := measureReal_union_add_inter (μ := bivariateNormalLaw r)
    (s := Iic a ×ˢ Iic b) (t := Iic a ×ˢ Ici b) (measurableSet_Iic.prod measurableSet_Ici)
  rw [hunion, hinter, hsingleton, add_zero] at hkey
  have hmargin : (bivariateNormalLaw r).real (Iic a ×ˢ (univ : Set ℝ)) = Phi a := by
    rw [show (Iic a ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) = Prod.fst ⁻¹' Iic a by ext p; simp,
      ← map_measureReal_apply measurable_fst measurableSet_Iic,
      map_fst_bivariateNormalLaw hr]
    simp [measureReal_def, Phi_def]
  rw [bivariateNormalCDF_eq_law, hflip, ← hkey, hmargin]

/-- **Joint survival identity**: `N₂(-a, -b; r) = 1 - Φ(a) - Φ(b) + N₂(a, b; r)`, derived purely
algebraically from the sign-flip identity `bivariateNormalCDF_flip_snd`, the symmetry
`bivariateNormalCDF_comm` and `Phi_neg` — no new measure-theoretic content. (Reading either side
as `P(X > a, Y > b)` is not stated here.) This is the identity that collapses the strike-side
terms of Stulz-style two-asset closed forms. -/
theorem bivariateNormalCDF_neg_neg (a b : ℝ) {r : ℝ} (hr : r ^ 2 ≤ 1) :
    bivariateNormalCDF (-a) (-b) r = 1 - Phi a - Phi b + bivariateNormalCDF a b r := by
  have hr' : (-r) ^ 2 ≤ 1 := by rwa [neg_sq]
  have h1 := bivariateNormalCDF_flip_snd a b hr
  have h2 := bivariateNormalCDF_flip_snd (-b) a hr'
  rw [neg_neg, Phi_neg, bivariateNormalCDF_comm (-b) a hr',
    bivariateNormalCDF_comm (-b) (-a) hr] at h2
  linarith

end MathFin

/-! ### The first threshold to `+∞` -/

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- **Sending the first threshold to `+∞` recovers the second margin**: `N₂(a, b; r) → Φ(b)` as
`a → ∞`, for every `r`. The quadrants `(-∞, a] × (-∞, b]` increase to `ℝ × (-∞, b]`
(continuity of measure from below, `tendsto_measure_iUnion_atTop`), whose
`bivariateNormalLaw r`-measure is `Φ(b)` by the second margin `map_snd_bivariateNormalLaw`,
which needs no condition on `r`. -/
theorem tendsto_bivariateNormalCDF_atTop_fst (b r : ℝ) :
    Tendsto (fun a ↦ bivariateNormalCDF a b r) atTop (𝓝 (Phi b)) := by
  have hmono : Monotone fun a : ℝ ↦ (Iic a ×ˢ Iic b : Set (ℝ × ℝ)) :=
    fun _ _ h ↦ prod_mono (Iic_subset_Iic.mpr h) subset_rfl
  have hU : (⋃ a : ℝ, (Iic a ×ˢ Iic b : Set (ℝ × ℝ))) = univ ×ˢ Iic b := by
    ext p
    simp only [mem_iUnion, mem_prod, mem_Iic, mem_univ, true_and]
    exact ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨p.1, le_rfl, h⟩⟩
  have hlim : Tendsto (fun a : ℝ ↦ bivariateNormalLaw r (Iic a ×ˢ Iic b)) atTop
      (𝓝 (bivariateNormalLaw r (univ ×ˢ Iic b))) := by
    rw [← hU]
    exact tendsto_measure_iUnion_atTop hmono
  have hPhi : Phi b = (bivariateNormalLaw r (univ ×ˢ Iic b)).toReal := by
    rw [show (univ ×ˢ Iic b : Set (ℝ × ℝ)) = Prod.snd ⁻¹' Iic b by ext p; simp,
      ← Measure.map_apply measurable_snd measurableSet_Iic, map_snd_bivariateNormalLaw, Phi_def]
  rw [hPhi]
  simp only [bivariateNormalCDF_eq_law, measureReal_def]
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim

/-! ### A Gaussian pair with any means, volatilities and correlation -/

/-- The Cholesky pair shifted and scaled: coordinate `i` is `μᵢ + σᵢ Zᵢ`, where `(Z₀, Z₁)` is the
pair of coordinates of `ℝ × ℝ`. Under `bivariateNormalLaw r` with `r² ≤ 1` it is a Gaussian pair
with means `μ`, volatilities `|σ|` and covariance `r σ₀ σ₁`, so a two-asset model with any such
parameters has a realization. -/
noncomputable def gaussianPair (μ σ : Fin 2 → ℝ) : Fin 2 → ℝ × ℝ → ℝ :=
  fun i q ↦ μ i + σ i * ![q.1, q.2] i

lemma gaussianPair_zero (μ σ : Fin 2 → ℝ) :
    gaussianPair μ σ 0 = fun q ↦ μ 0 + σ 0 * q.1 := rfl

lemma gaussianPair_one (μ σ : Fin 2 → ℝ) :
    gaussianPair μ σ 1 = fun q ↦ μ 1 + σ 1 * q.2 := rfl

/-- **The pair is jointly Gaussian**, for every `r`: it is a translate of a continuous linear
image of the Gaussian measure `bivariateNormalLaw r`. -/
theorem hasGaussianLaw_gaussianPair (r : ℝ) (μ σ : Fin 2 → ℝ) :
    HasGaussianLaw (fun q i ↦ gaussianPair μ σ i q) (bivariateNormalLaw r) := by
  let L : ℝ × ℝ →L[ℝ] Fin 2 → ℝ :=
    ContinuousLinearMap.pi ![σ 0 • ContinuousLinearMap.fst ℝ ℝ ℝ,
      σ 1 • ContinuousLinearMap.snd ℝ ℝ ℝ]
  have h : (fun q i ↦ gaussianPair μ σ i q) = (μ + ·) ∘ L := by
    ext q i
    fin_cases i <;> simp [gaussianPair, L]
  refine ⟨by rw [h]; fun_prop, ?_⟩
  rw [h, ← Measure.map_map (measurable_const_add μ) L.measurable]
  infer_instance

lemma memLp_gaussianPair (r : ℝ) (μ σ : Fin 2 → ℝ) (i : Fin 2) :
    MemLp (gaussianPair μ σ i) 2 (bivariateNormalLaw r) := by
  revert i
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · rw [gaussianPair_zero]
    exact (memLp_const (μ 0)).add ((memLp_fst_bivariateNormalLaw r).const_mul (σ 0))
  · rw [gaussianPair_one]
    exact (memLp_const (μ 1)).add ((memLp_snd_bivariateNormalLaw r).const_mul (σ 1))

lemma integral_gaussianPair (r : ℝ) (μ σ : Fin 2 → ℝ) (i : Fin 2) :
    ∫ q, gaussianPair μ σ i q ∂bivariateNormalLaw r = μ i := by
  have h₀ := (memLp_fst_bivariateNormalLaw r).integrable one_le_two
  have h₁ := (memLp_snd_bivariateNormalLaw r).integrable one_le_two
  revert i
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · simp [gaussianPair_zero, integral_add (integrable_const _) (h₀.const_mul _),
      integral_const_mul, integral_fst_bivariateNormalLaw]
  · simp [gaussianPair_one, integral_add (integrable_const _) (h₁.const_mul _),
      integral_const_mul, integral_snd_bivariateNormalLaw]

lemma variance_gaussianPair {r : ℝ} (hr : r ^ 2 ≤ 1) (μ σ : Fin 2 → ℝ) (i : Fin 2) :
    Var[gaussianPair μ σ i; bivariateNormalLaw r] = σ i ^ 2 := by
  revert i
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · rw [gaussianPair_zero, variance_const_add (by fun_prop), variance_const_mul,
      variance_fst_bivariateNormalLaw hr]
    simp
  · rw [gaussianPair_one, variance_const_add (by fun_prop), variance_const_mul,
      variance_snd_bivariateNormalLaw]
    simp

/-- **The parameter `r` is the correlation of the pair**: `Cov = r σ₀ σ₁`, for every `r`. -/
theorem covariance_gaussianPair (r : ℝ) (μ σ : Fin 2 → ℝ) :
    cov[gaussianPair μ σ 0, gaussianPair μ σ 1; bivariateNormalLaw r] = r * σ 0 * σ 1 := by
  have h₀ := ((memLp_fst_bivariateNormalLaw r).const_mul (σ 0)).integrable one_le_two
  have h₁ := ((memLp_snd_bivariateNormalLaw r).const_mul (σ 1)).integrable one_le_two
  rw [gaussianPair_zero, gaussianPair_one, covariance_const_add_left h₀,
    covariance_const_add_right h₁, covariance_const_mul_left, covariance_const_mul_right,
    covariance_fst_snd_bivariateNormalLaw]
  ring

end MathFin

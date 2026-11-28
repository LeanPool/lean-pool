/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.ScalingFunction

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The cascade algorithm and the support of the scaling function

For a Daubechies mask of order `N` with filter coefficients `c_k` (`Daubechies.coeff`), symbol
`m_0` (`Daubechies.symbol`) and symbol product `Φ(ξ) = ∏_{j ≥ 0} m_0(ξ/2^(j+1))`
(`Daubechies.symbolProduct`), the scaling function is `φ = 𝓕⁻ Φ` (`Daubechies.scalingFun`).
This file proves that `φ` vanishes outside `[0, 2N - 1]` and that `𝓕 φ = Φ`, with the help of
the **cascade algorithm**

`η_0 = 1_[0,1)`, `η_(n+1)(x) = ∑_{k=0}^{2N-1} c_k η_n(2x - k)` (`Daubechies.cascade`).

* **Support.** Every `η_n` vanishes outside `[0, 2N - 1]` (`Daubechies.cascade_eq_zero`): for
  `0 ≤ k ≤ 2N - 1`, `2x - k ∈ [0, 2N - 1]` forces `x ∈ [0, 2N - 1]`. Every `η_n` is integrable
  (`Daubechies.integrable_cascade`).
* **Fourier transform.** Dilation and translation turn the recursion into
  `𝓕 η_(n+1)(ξ) = m_0(ξ/2) 𝓕 η_n(ξ/2)` (`Daubechies.fourier_cascade_succ`), hence
  `𝓕 η_n(ξ) = ∏_{j<n} m_0(ξ/2^(j+1)) · 𝓕 η_0(ξ/2^n)` (`Daubechies.fourier_cascade`). Since
  `|m_0| ≤ 1` and `|𝓕 η_0| ≤ ∫ η_0 = 1`, `|𝓕 η_n| ≤ 1` (`Daubechies.norm_fourier_cascade_le_one`).
  The partial products converge to `Φ`, and `𝓕 η_0` is continuous with `𝓕 η_0(0) = 1`, so
  `𝓕 η_n(ξ) → Φ(ξ)` for every `ξ` (`Daubechies.tendsto_fourier_cascade`).
* **Convergence against Schwartz functions.** For `N ≥ 2` and every Schwartz function `ψ`,
  `∫ η_n ψ = ∫ 𝓕 η_n · 𝓕⁻ ψ → ∫ Φ · 𝓕⁻ ψ = ∫ φ ψ` (`Daubechies.tendsto_integral_cascade_mul`),
  by the multiplication formula (`Real.integral_mul_schwartz_eq`, `Real.integral_fourierInv_mul`)
  and dominated convergence with the integrable bound `|𝓕⁻ ψ|`.
* **Compact support of `φ`.** For `ψ` supported in the open set `ℝ \ [0, 2N - 1]` every integral
  `∫ η_n ψ` vanishes, so `∫ φ ψ = 0`, and the fundamental lemma
  (`Real.eqOn_zero_of_integral_mul_schwartz_eq_zero`) gives `φ = 0` outside `[0, 2N - 1]`
  (`Daubechies.scalingFun_eq_zero`), and by continuity also at the endpoints `0` and `2N - 1`
  (`Daubechies.scalingFun_eq_zero_of_notMem_Ioo`). Hence `φ` has compact support
  (`Daubechies.hasCompactSupport_scalingFun`); as a continuous function with compact support it
  is integrable and lies in every `L^p` (`Daubechies.integrable_scalingFun`,
  `Daubechies.memLp_scalingFun`).
* **Fourier inversion.** `𝓕 Φ(ξ) = φ(-ξ)` is integrable, so the inversion theorem gives
  `𝓕 φ = Φ` (`Daubechies.fourier_scalingFun`), and `∫ φ = 𝓕 φ(0) = Φ(0) = 1`
  (`Daubechies.integral_scalingFun`, with `𝓕 f(0) = ∫ f` from `Real.fourier_apply_zero`).
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped Real FourierTransform SchwartzMap ENNReal

namespace Daubechies

/-! ### The cascade -/

variable {N : ℕ} (m : Mask N)

/-- **The cascade algorithm** of a mask with filter coefficients `c_k`: `η_0 = 1_[0,1)` is the
indicator function of `[0, 1)`, and `η_(n+1)(x) = ∑_{k=0}^{2N-1} c_k η_n(2x - k)`. For `N ≥ 2`
the functions `η_n` converge to the scaling function `φ` against every Schwartz function
(`Daubechies.tendsto_integral_cascade_mul`). -/
noncomputable def cascade : ℕ → ℝ → ℂ
  | 0 => (Set.Ico (0 : ℝ) 1).indicator 1
  | n + 1 => fun x => ∑ k ∈ Finset.range (2 * N), (coeff m k : ℂ) * cascade n (2 * x - k)

/-- `η_0 = 1_[0,1)`, the indicator function of `[0, 1)`. -/
theorem cascade_zero : cascade m 0 = (Set.Ico (0 : ℝ) 1).indicator 1 := rfl

/-- The cascade recursion as an identity of functions:
`η_(n+1) = (x ↦ ∑_{k=0}^{2N-1} c_k η_n(2x - k))`. -/
theorem cascade_succ (n : ℕ) :
    cascade m (n + 1) =
      fun x => ∑ k ∈ Finset.range (2 * N), (coeff m k : ℂ) * cascade m n (2 * x - k) := rfl

/-- **The cascade recursion** `η_(n+1)(x) = ∑_{k=0}^{2N-1} c_k η_n(2x - k)` for every
`x ∈ ℝ`. -/
theorem cascade_succ_apply (n : ℕ) (x : ℝ) :
    cascade m (n + 1) x =
      ∑ k ∈ Finset.range (2 * N), (coeff m k : ℂ) * cascade m n (2 * x - k) := rfl

/-! ### Support and integrability of the cascade -/

/-- If `0 ≤ k ≤ b` and `2x - k ∈ [0, b]`, then `x ∈ [0, b]`: `x ≥ k/2 ≥ 0` and
`x ≤ (b + k)/2 ≤ b`. For `b = 2N - 1` this is the step of the support argument for the cascade:
no map `x ↦ 2x - k` with `0 ≤ k ≤ 2N - 1` sends a point outside `[0, 2N - 1]` into
`[0, 2N - 1]`. -/
theorem mem_Icc_of_two_mul_sub_mem_Icc {x k b : ℝ} (hk : 0 ≤ k) (hkb : k ≤ b)
    (h : 2 * x - k ∈ Set.Icc 0 b) : x ∈ Set.Icc 0 b :=
  ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **The cascade functions vanish outside `[0, 2N - 1]`**: `η_n(x) = 0` for every `n` and every
`x ∉ [0, 2N - 1]`. By induction on `n`: `[0, 1) ⊆ [0, 2N - 1]` since `N ≥ 1`
(`Daubechies.Mask.one_le`), and for `x ∉ [0, 2N - 1]` no point `2x - k` with `0 ≤ k ≤ 2N - 1`
lies in `[0, 2N - 1]` (`Daubechies.mem_Icc_of_two_mul_sub_mem_Icc`). -/
theorem cascade_eq_zero (n : ℕ) {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) (2 * N - 1)) :
    cascade m n x = 0 := by
  induction n generalizing x with
  | zero =>
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast m.one_le
    exact Set.indicator_of_notMem (fun h : x ∈ Set.Ico (0 : ℝ) 1 => hx ⟨h.1, by linarith [h.2]⟩) _
  | succ n ih =>
    rw [cascade_succ_apply]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : (k : ℝ) + 1 ≤ 2 * N := by exact_mod_cast Finset.mem_range.1 hk
    rw [ih (fun h => hx (mem_Icc_of_two_mul_sub_mem_Icc k.cast_nonneg (by linarith) h)),
      mul_zero]

/-- If `f : ℝ → ℂ` is integrable, then so is `x ↦ c f(2x - b)`, for all `c ∈ ℂ` and `b ∈ ℝ`
(Mathlib's `MeasureTheory.Integrable.comp_sub_right` and
`MeasureTheory.Integrable.comp_mul_left'`). -/
theorem integrable_const_mul_comp_two_mul_sub {f : ℝ → ℂ} (hf : Integrable f) (c : ℂ) (b : ℝ) :
    Integrable (fun x => c * f (2 * x - b)) :=
  ((hf.comp_sub_right b).comp_mul_left' two_ne_zero).const_mul c

/-- **The cascade functions are integrable**, by induction on `n`: `1_[0,1)` is integrable, and
`η_(n+1)` is a finite sum of the integrable functions `x ↦ c_k η_n(2x - k)`. -/
theorem integrable_cascade (n : ℕ) : Integrable (cascade m n) := by
  induction n with
  | zero =>
    exact (integrable_indicator_iff measurableSet_Ico).2
      (integrableOn_const measure_Ico_lt_top.ne)
  | succ n ih =>
    rw [cascade_succ]
    exact integrable_finsetSum _ fun k _ => integrable_const_mul_comp_two_mul_sub ih _ _

/-! ### The Fourier transform of the cascade -/

/-- **The cascade recursion on the Fourier side**: `𝓕 η_(n+1)(ξ) = m_0(ξ/2) 𝓕 η_n(ξ/2)` for
every `ξ ∈ ℝ`. The transform of `x ↦ η_n(2x - k)` is `(1/2) e^(-2πik(ξ/2)) 𝓕 η_n(ξ/2)`
(`Real.fourier_comp_mul_sub_apply`), and `(1/2) ∑_k c_k e^(-2πik(ξ/2)) = m_0(ξ/2)`
(`Daubechies.symbol_eq_sum`). -/
theorem fourier_cascade_succ (n : ℕ) (ξ : ℝ) :
    𝓕 (cascade m (n + 1)) ξ = symbol m (ξ / 2) * 𝓕 (cascade m n) (ξ / 2) := by
  rw [cascade_succ, Real.fourier_sum_apply _ (fun (k : ℕ) _ =>
      integrable_const_mul_comp_two_mul_sub (integrable_cascade m n) _ _),
    symbol_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.fourier_const_mul_apply, Real.fourier_comp_mul_sub_apply _ two_pos, expFreq_pow,
    expFreq]
  push_cast
  rw [show -(2 * (π : ℂ) * k * (ξ / 2) * Complex.I) = -(2 * π * (k * (ξ / 2))) * Complex.I by
    ring]
  ring

/-- **The Fourier transform of the cascade**:
`𝓕 η_n(ξ) = ∏_{j<n} m_0(ξ/2^(j+1)) · 𝓕 η_0(ξ/2^n)` for every `n` and every `ξ ∈ ℝ`, by induction
with `Daubechies.fourier_cascade_succ` and the splitting of the first factor of the product
(`Daubechies.prod_range_succ_symbol`). -/
theorem fourier_cascade (n : ℕ) (ξ : ℝ) :
    𝓕 (cascade m n) ξ =
      (∏ j ∈ Finset.range n, symbol m (ξ / 2 ^ (j + 1))) * 𝓕 (cascade m 0) (ξ / 2 ^ n) := by
  induction n generalizing ξ with
  | zero => simp
  | succ n ih =>
    have h : ξ / 2 / 2 ^ n = ξ / 2 ^ (n + 1) := by rw [div_div, ← pow_succ']
    rw [fourier_cascade_succ, ih, prod_range_succ_symbol, h, mul_assoc]

/-- The Fourier transform of every cascade function is continuous, since `η_n` is integrable
(`Real.continuous_fourier_of_integrable`). -/
theorem continuous_fourier_cascade (n : ℕ) : Continuous (𝓕 (cascade m n)) :=
  Real.continuous_fourier_of_integrable (integrable_cascade m n)

/-- `∫ η_0 = ∫_0^1 1 dx = 1`. -/
theorem integral_cascade_zero : ∫ x, cascade m 0 x = 1 := by
  rw [cascade_zero, integral_indicator measurableSet_Ico]
  simp

/-- `∫ |η_0| = 1`, since `|η_0| = 1_[0,1)`. -/
theorem integral_norm_cascade_zero : ∫ x, ‖cascade m 0 x‖ = 1 := by
  rw [cascade_zero]
  simp [norm_indicator_eq_indicator_norm, integral_indicator measurableSet_Ico]

/-- `𝓕 η_0(0) = ∫ η_0 = 1` (`Real.fourier_apply_zero`). -/
theorem fourier_cascade_zero_apply_zero : 𝓕 (cascade m 0) 0 = 1 := by
  rw [Real.fourier_apply_zero, integral_cascade_zero]

/-- `|𝓕 η_0(ξ)| ≤ ∫ |η_0| = 1` for every `ξ ∈ ℝ` (`Real.norm_fourier_le_integral_norm`). -/
theorem norm_fourier_cascade_zero_le_one (ξ : ℝ) : ‖𝓕 (cascade m 0) ξ‖ ≤ 1 :=
  (Real.norm_fourier_le_integral_norm _ ξ).trans (integral_norm_cascade_zero m).le

/-- **The Fourier transforms of the cascade are bounded by `1`**: `|𝓕 η_n(ξ)| ≤ 1` for every `n`
and every `ξ ∈ ℝ`. In `Daubechies.fourier_cascade` the partial products of the symbol have
modulus at most `1` (`Daubechies.norm_prod_symbol_le_one`), and `|𝓕 η_0| ≤ 1`. -/
theorem norm_fourier_cascade_le_one (n : ℕ) (ξ : ℝ) : ‖𝓕 (cascade m n) ξ‖ ≤ 1 := by
  rw [fourier_cascade, norm_mul, ← one_mul (1 : ℝ)]
  exact mul_le_mul (norm_prod_symbol_le_one m ξ n) (norm_fourier_cascade_zero_le_one m _)
    (norm_nonneg _) zero_le_one

/-- **The Fourier transforms of the cascade converge to the symbol product**: `𝓕 η_n(ξ) → Φ(ξ)`
as `n → ∞`, for every `ξ ∈ ℝ`. In `𝓕 η_n(ξ) = ∏_{j<n} m_0(ξ/2^(j+1)) · 𝓕 η_0(ξ/2^n)` the
partial products converge to `Φ(ξ)` (`Daubechies.tendsto_prod_symbol`), and
`𝓕 η_0(ξ/2^n) → 𝓕 η_0(0) = 1` since `𝓕 η_0` is continuous. -/
theorem tendsto_fourier_cascade (ξ : ℝ) :
    Tendsto (fun n => 𝓕 (cascade m n) ξ) atTop (𝓝 (symbolProduct m ξ)) := by
  have h0 : Tendsto (fun n : ℕ => ξ / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have h1 : Tendsto (fun n : ℕ => 𝓕 (cascade m 0) (ξ / 2 ^ n)) atTop (𝓝 1) := by
    rw [← fourier_cascade_zero_apply_zero m]
    exact ((continuous_fourier_cascade m 0).tendsto 0).comp h0
  have h := (tendsto_prod_symbol m ξ).mul h1
  rw [mul_one] at h
  exact h.congr fun n => (fourier_cascade m n ξ).symm

/-! ### Convergence against Schwartz functions -/

/-- **The cascade converges to the scaling function against Schwartz functions**: for a mask of
order `N ≥ 2` and every Schwartz function `ψ`, `∫ η_n ψ → ∫ φ ψ` as `n → ∞`. The
multiplication formula gives `∫ η_n ψ = ∫ 𝓕 η_n · 𝓕⁻ ψ` (`Real.integral_mul_schwartz_eq`). These
integrands converge pointwise to `Φ · 𝓕⁻ ψ` (`Daubechies.tendsto_fourier_cascade`) and are
bounded by the integrable function `|𝓕⁻ ψ|` (`Daubechies.norm_fourier_cascade_le_one`), so
dominated convergence (Mathlib's `MeasureTheory.tendsto_integral_of_dominated_convergence`) gives
the limit `∫ Φ · 𝓕⁻ ψ = ∫ 𝓕⁻ Φ · ψ = ∫ φ ψ` (`Real.integral_fourierInv_mul`, which needs
`Φ ∈ L¹`, `Daubechies.integrable_symbolProduct`). -/
theorem tendsto_integral_cascade_mul (hN : 2 ≤ N) (ψ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun n => ∫ x, cascade m n x * ψ x) atTop (𝓝 (∫ x, scalingFun m x * ψ x)) := by
  have h1 : ∀ n, ∫ x, cascade m n x * ψ x = ∫ ξ, 𝓕 (cascade m n) ξ * 𝓕⁻ ψ ξ := fun n =>
    Real.integral_mul_schwartz_eq (integrable_cascade m n) ψ
  have h2 : ∫ x, scalingFun m x * ψ x = ∫ ξ, symbolProduct m ξ * 𝓕⁻ ψ ξ := by
    rw [scalingFun, Real.integral_fourierInv_mul (integrable_symbolProduct m hN) ψ.integrable,
      SchwartzMap.fourierInv_coe]
  simp_rw [h1, h2]
  refine tendsto_integral_of_dominated_convergence (fun ξ => ‖𝓕⁻ ψ ξ‖)
    (fun n => ((continuous_fourier_cascade m n).mul (𝓕⁻ ψ).continuous).aestronglyMeasurable)
    (𝓕⁻ ψ).integrable.norm (fun n => Eventually.of_forall fun ξ => ?_)
    (Eventually.of_forall fun ξ => (tendsto_fourier_cascade m ξ).mul_const _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_fourier_cascade_le_one m n ξ)

/-! ### The support of the scaling function -/

/-- `∫ η_n g = 0` for every `n` and every function `g : ℝ → ℂ` that vanishes on `[0, 2N - 1]`:
the product `η_n g` vanishes everywhere (`Daubechies.cascade_eq_zero`). -/
theorem integral_cascade_mul_eq_zero (n : ℕ) {g : ℝ → ℂ}
    (hg : ∀ x ∈ Set.Icc (0 : ℝ) (2 * N - 1), g x = 0) :
    ∫ x, cascade m n x * g x = 0 := by
  have h : ∀ x, cascade m n x * g x = 0 := fun x => by
    by_cases hx : x ∈ Set.Icc (0 : ℝ) (2 * N - 1)
    · rw [hg x hx, mul_zero]
    · rw [cascade_eq_zero m n hx, zero_mul]
  simp only [h, integral_zero]

/-- **The scaling function vanishes outside `[0, 2N - 1]`**: for a mask of order `N ≥ 2`,
`φ(x) = 0` for every `x ∉ [0, 2N - 1]`. For a Schwartz function `ψ` with support in the open set
`ℝ \ [0, 2N - 1]` every integral `∫ η_n ψ` vanishes (`Daubechies.integral_cascade_mul_eq_zero`),
so their limit `∫ φ ψ` (`Daubechies.tendsto_integral_cascade_mul`) is `0`. The continuous
function `φ` therefore vanishes on the open set, by the fundamental lemma
(`Real.eqOn_zero_of_integral_mul_schwartz_eq_zero`). -/
theorem scalingFun_eq_zero (hN : 2 ≤ N) {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) (2 * N - 1)) :
    scalingFun m x = 0 := by
  refine Real.eqOn_zero_of_integral_mul_schwartz_eq_zero (continuous_scalingFun m hN)
    isClosed_Icc.isOpen_compl (fun ψ _ hψ => ?_) x hx
  have h0 : ∀ n, ∫ x, cascade m n x * ψ x = 0 := fun n =>
    integral_cascade_mul_eq_zero m n fun y hy =>
      image_eq_zero_of_notMem_tsupport fun h => hψ h hy
  have h := tendsto_integral_cascade_mul m hN ψ
  simp only [h0] at h
  simp_rw [mul_comm (ψ _)]
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- **The scaling function vanishes at the endpoints as well**: `φ(x) = 0` for every
`x ∉ (0, 2N - 1)`, for `N ≥ 2`. The zero set of the continuous function `φ` is closed and
contains the open set `ℝ \ [0, 2N - 1]` (`Daubechies.scalingFun_eq_zero`), hence also its closure
`ℝ \ (0, 2N - 1)`. -/
theorem scalingFun_eq_zero_of_notMem_Ioo (hN : 2 ≤ N) {x : ℝ}
    (hx : x ∉ Set.Ioo (0 : ℝ) (2 * N - 1)) : scalingFun m x = 0 := by
  have h : closure (Set.Icc (0 : ℝ) (2 * N - 1))ᶜ ⊆ {y | scalingFun m y = 0} :=
    closure_minimal (fun y hy => scalingFun_eq_zero m hN hy)
      (isClosed_eq (continuous_scalingFun m hN) continuous_const)
  rw [closure_compl, interior_Icc] at h
  exact h hx

/-- The closed support of the scaling function lies in `[0, 2N - 1]`, for `N ≥ 2`
(`Daubechies.scalingFun_eq_zero`). -/
theorem tsupport_scalingFun_subset (hN : 2 ≤ N) :
    tsupport (scalingFun m) ⊆ Set.Icc (0 : ℝ) (2 * N - 1) :=
  closure_minimal (fun _ hx => by_contra fun h => hx (scalingFun_eq_zero m hN h)) isClosed_Icc

/-- **The scaling function has compact support**, for `N ≥ 2`: it vanishes outside the compact
interval `[0, 2N - 1]` (`Daubechies.scalingFun_eq_zero`). -/
theorem hasCompactSupport_scalingFun (hN : 2 ≤ N) : HasCompactSupport (scalingFun m) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => scalingFun_eq_zero m hN hx

/-- **The scaling function is integrable**, for `N ≥ 2`: it is continuous with compact support
(Mathlib's `Continuous.integrable_of_hasCompactSupport`). -/
theorem integrable_scalingFun (hN : 2 ≤ N) : Integrable (scalingFun m) :=
  (continuous_scalingFun m hN).integrable_of_hasCompactSupport
    (hasCompactSupport_scalingFun m hN)

/-- **The scaling function lies in every `L^p`**: `φ ∈ L^p(ℝ)` for every exponent `p ∈ [0, ∞]`,
for `N ≥ 2`, since it is continuous with compact support (Mathlib's
`Continuous.memLp_of_hasCompactSupport`). -/
theorem memLp_scalingFun (hN : 2 ≤ N) (p : ℝ≥0∞) : MemLp (scalingFun m) p :=
  (continuous_scalingFun m hN).memLp_of_hasCompactSupport (hasCompactSupport_scalingFun m hN)

/-! ### The Fourier transform of the scaling function -/

/-- `𝓕 Φ(ξ) = φ(-ξ)` for every `ξ ∈ ℝ`, since `𝓕⁻ Φ(x) = 𝓕 Φ(-x)` (Mathlib's
`Real.fourierInv_eq_fourier_neg`). -/
theorem fourier_symbolProduct_apply (ξ : ℝ) : 𝓕 (symbolProduct m) ξ = scalingFun m (-ξ) := by
  rw [scalingFun, Real.fourierInv_eq_fourier_neg, neg_neg]

/-- For `N ≥ 2` the Fourier transform `𝓕 Φ` of the symbol product is integrable:
`𝓕 Φ(ξ) = φ(-ξ)` (`Daubechies.fourier_symbolProduct_apply`), and `φ` is integrable. -/
theorem integrable_fourier_symbolProduct (hN : 2 ≤ N) : Integrable (𝓕 (symbolProduct m)) := by
  rw [funext (fourier_symbolProduct_apply m)]
  exact (integrable_scalingFun m hN).comp_neg

/-- **The Fourier transform of the scaling function is the symbol product**: `𝓕 φ = Φ` for
`N ≥ 2`. The function `Φ` is continuous and integrable, and so is `𝓕 Φ`
(`Daubechies.integrable_fourier_symbolProduct`), so the inversion theorem `𝓕 (𝓕⁻ Φ) = Φ` applies
(Mathlib's `Continuous.fourier_fourierInv_eq`). -/
theorem fourier_scalingFun (hN : 2 ≤ N) : 𝓕 (scalingFun m) = symbolProduct m :=
  (continuous_symbolProduct m).fourier_fourierInv_eq (integrable_symbolProduct m hN)
    (integrable_fourier_symbolProduct m hN)

/-- **The scaling function has integral `1`**: `∫ φ = 𝓕 φ(0) = Φ(0) = 1` for `N ≥ 2`
(`Real.fourier_apply_zero`, `Daubechies.fourier_scalingFun`, `Daubechies.symbolProduct_zero`). -/
theorem integral_scalingFun (hN : 2 ≤ N) : ∫ x, scalingFun m x = 1 := by
  rw [← Real.fourier_apply_zero, fourier_scalingFun m hN, symbolProduct_zero]

end Daubechies

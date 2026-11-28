/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.SymbolProduct
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.TransferOperator
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Function.L2Space

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The decay of the symbol product

For a Daubechies mask of order `N` with symbol product `Φ(ξ) = ∏_{j ≥ 0} m_0(ξ/2^(j+1))`
(`Daubechies.symbolProduct`), a growth bound `T^n 1 ≤ C λ^n` for the transfer operator `T`
(`Daubechies.TransferGrowth N λ C`) gives the decay of `Φ`:

* `∫ (1 + |ξ|)^(2s) |Φ(ξ)|² dξ < ∞` for every real `s < N - log₄ λ`
  (`Daubechies.integrable_rpow_mul_normSq`);
* `∫ (1 + |ξ|)^a |Φ(ξ)| dξ < ∞` for every real `a < N - log₄ λ - 1/2`
  (`Daubechies.integrable_rpow_mul_norm`), in particular `Φ ∈ L¹` if `N - log₄ λ - 1/2 > 0`
  (`Daubechies.integrable_symbolProduct_of_growth`).

The crude growth bound `λ = 2 C(2N - 1, N)`, `C = 1` (`Daubechies.transferGrowth_crude`)
satisfies `log₄(2 C(2N - 1, N)) < N - 1/2` for `N ≥ 2`
(`Daubechies.logb_four_two_mul_choose_lt`), so the cases `a = 0` and `s = 0` give `Φ ∈ L¹` and
`Φ ∈ L²` for every `N ≥ 2` (`Daubechies.integrable_symbolProduct`,
`Daubechies.memLp_symbolProduct_two`).

**The annuli.** The dyadic annuli `A_n = {2^n/4 < |ξ| ≤ 2^n/2}`, `n ∈ ℕ` (`Daubechies.annulus`),
together with `[-1/4, 1/4]` cover `ℝ` (`Daubechies.univ_subset_Icc_union_annulus`). For
`ξ ∈ A_n`, `|sinc(πξ)| ≤ 1/(π|ξ|) < 4/(π 2^n)`, and the product formula
`|Φ(ξ)|² = sinc(πξ)^(2N) ∏_{j ≥ 0} P(ξ/2^(j+1))` with the tail bound of
`Daubechies.normSq_symbolProduct_le` gives
`|Φ(ξ)|² ≤ exp(C(2N - 1, N) π²/12) (4/(π 2^n))^(2N) ∏_{j<n} P(ξ/2^(j+1))`
(`Daubechies.normSq_symbolProduct_le_of_mem_annulus`). The finite product is nonnegative, and its
integral over `[-2^n/2, 2^n/2] ⊇ A_n` equals `∫_{-1/2}^{1/2} T^n 1 ≤ C λ^n`
(`Daubechies.TransferGrowth.setIntegral_prod_daubFun_le`). Hence
`∫_{A_n} |Φ|² ≤ exp(C(2N - 1, N) π²/12) (4/(π 2^n))^(2N) C λ^n`
(`Daubechies.integral_annulus_normSq_le`), a geometric sequence in `n` with ratio `λ/4^N`.

**Summation.** A continuous function whose integrals over the annuli decay geometrically is
integrable (`Daubechies.integrable_of_integral_annulus_le`). On `A_n` the weight
`(1 + |ξ|)^(2s)` is at most `4^|2s| 2^(2sn)` (`Daubechies.one_add_abs_rpow_le_of_mem_annulus`),
so the weighted integrals over the annuli decay with ratio `2^(2s) λ/4^N`, which is less than `1`
for `s < N - log₄ λ`. The `L¹` bound follows from the `L²` bound pointwise: for
`a + 1/2 < b < N - log₄ λ`,
`(1 + |ξ|)^a |Φ(ξ)| ≤ (1 + |ξ|)^(-2(b - a)) + (1 + |ξ|)^(2b) |Φ(ξ)|²`
(`Daubechies.rpow_mul_le_rpow_add_rpow_mul_sq`), and `(1 + |ξ|)^(-r)` is integrable for `r > 1`
(Mathlib's `integrable_one_add_norm`).
-/

@[expose] public section

open Filter MeasureTheory
open scoped Real

namespace Daubechies

/-! ### The finite dyadic products of `P` -/

/-- The finite dyadic products `∏_{j<n} P(ξ/2^(j+1))` of the trigonometric Daubechies polynomial
`P = Daubechies.daubFun N` are nonnegative, since `P ≥ 0`. -/
theorem prod_daubFun_nonneg (N n : ℕ) (ξ : ℝ) :
    0 ≤ ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1)) :=
  Finset.prod_nonneg fun _ _ => daubFun_nonneg N _

/-- The finite dyadic products `ξ ↦ ∏_{j<n} P(ξ/2^(j+1))` are continuous. -/
theorem continuous_prod_daubFun (N n : ℕ) :
    Continuous fun ξ : ℝ => ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1)) :=
  continuous_finsetProd _ fun _ _ => (continuous_daubFun N).comp (continuous_id.div_const _)

/-! ### Growth bounds -/

/-- Under a growth bound `T^n 1 ≤ C λ^n`, the integral of `∏_{j<n} P(ξ/2^(j+1))` over every set
`s ⊆ [-2^n/2, 2^n/2]` is at most `C λ^n`: the integrand is nonnegative, so the integral over `s`
is at most the integral over the whole interval, which is at most `C λ^n`
(`Daubechies.TransferGrowth.integral_prod_daubFun_le`). -/
theorem TransferGrowth.setIntegral_prod_daubFun_le {N : ℕ} {lam C : ℝ}
    (hg : TransferGrowth N lam C) (n : ℕ) {s : Set ℝ}
    (hs : s ⊆ Set.Icc (-(2 ^ n / 2)) (2 ^ n / 2)) :
    ∫ ξ in s, ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1)) ≤ C * lam ^ n := by
  have hle : -(2 ^ n / 2 : ℝ) ≤ 2 ^ n / 2 := by
    have : (0 : ℝ) ≤ 2 ^ n / 2 := by positivity
    linarith
  calc ∫ ξ in s, ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1))
      ≤ ∫ ξ in Set.Icc (-(2 ^ n / 2)) (2 ^ n / 2),
          ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1)) :=
        setIntegral_mono_set (continuous_prod_daubFun N n).integrableOn_Icc
          (Eventually.of_forall fun ξ => prod_daubFun_nonneg N n ξ)
          (Eventually.of_forall fun _ hx => hs hx)
    _ = ∫ ξ in -(2 ^ n / 2 : ℝ)..2 ^ n / 2,
          ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1)) := by
        rw [intervalIntegral.integral_of_le hle, integral_Icc_eq_integral_Ioc]
    _ ≤ C * lam ^ n := hg.integral_prod_daubFun_le n

/-- `log₄(2 C(2N - 1, N)) < N - 1/2` for `N ≥ 2`. It follows from `C(2N - 1, N) < 4^(N - 1)`
(`Daubechies.choose_lt_four_pow`), since `2 · 4^(N - 1) = 4^(N - 1/2)`. -/
theorem logb_four_two_mul_choose_lt {N : ℕ} (hN : 2 ≤ N) :
    Real.logb 4 (2 * ((2 * N - 1).choose N : ℝ)) < N - 1 / 2 := by
  have hC : ((2 * N - 1).choose N : ℝ) < 4 ^ (N - 1) := by
    exact_mod_cast choose_lt_four_pow hN
  have hpos : (0 : ℝ) < 2 * ((2 * N - 1).choose N : ℝ) := by
    have := Nat.choose_pos (show N ≤ 2 * N - 1 by omega)
    positivity
  have h4 : (4 : ℝ) ^ ((N : ℝ) - 1 / 2) = 2 * 4 ^ (N - 1) := by
    have hN' : (N : ℝ) - 1 / 2 = ((N - 1 : ℕ) : ℝ) + 1 / 2 := by
      rw [Nat.cast_sub (by omega)]
      ring
    have h2 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [hN', Real.rpow_add (by norm_num), Real.rpow_natCast, h2, mul_comm]
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hpos, h4]
  linarith

/-- If `λ > 0` and `s < N - log₄ λ`, then `2^(2s) λ < 4^N`: the hypothesis says
`log₄ λ < N - s`, that is `λ < 4^(N - s) = 4^N/4^s`, and `2^(2s) = 4^s`. -/
theorem two_rpow_two_mul_mul_lt {N : ℕ} {lam s : ℝ} (hlam : 0 < lam)
    (hs : s < N - Real.logb 4 lam) : (2 : ℝ) ^ (2 * s) * lam < 4 ^ N := by
  have h : Real.logb 4 lam < N - s := by linarith
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hlam, Real.rpow_sub (by norm_num),
    Real.rpow_natCast, lt_div_iff₀ (by positivity)] at h
  rw [Real.rpow_mul (by norm_num), show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num]
  linarith

/-! ### The dyadic annuli -/

/-- **The dyadic annulus** `A_n = {ξ ∈ ℝ : 2^n/4 < |ξ| ≤ 2^n/2}` for `n ∈ ℕ`. The annuli
`A_0, A_1, …` cover `{|ξ| > 1/4}` (`Daubechies.exists_mem_annulus`). -/
def annulus (n : ℕ) : Set ℝ := {ξ | 2 ^ n / 4 < |ξ| ∧ |ξ| ≤ 2 ^ n / 2}

/-- The annuli are measurable sets. -/
theorem measurableSet_annulus (n : ℕ) : MeasurableSet (annulus n) :=
  (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

/-- The annulus `A_n` lies in the interval `[-2^n/2, 2^n/2]`. -/
theorem annulus_subset_Icc (n : ℕ) : annulus n ⊆ Set.Icc (-(2 ^ n / 2)) (2 ^ n / 2) :=
  fun _ hξ => abs_le.1 hξ.2

/-- **The annuli cover `{|ξ| > 1/4}`**: for `|ξ| > 1/4` the least `n` with `|ξ| ≤ 2^n/2`
satisfies `2^n/4 < |ξ|` (for `n = 0` by hypothesis, for `n ≥ 1` by minimality), so `ξ ∈ A_n`. -/
theorem exists_mem_annulus {ξ : ℝ} (h : 1 / 4 < |ξ|) : ∃ n : ℕ, ξ ∈ annulus n := by
  classical
  have hex : ∃ n : ℕ, |ξ| ≤ 2 ^ n / 2 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * |ξ|) one_lt_two
    exact ⟨n, by linarith⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero]
    exact h
  · have hmin := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    rw [not_le] at hmin
    have h2 : (2 : ℝ) ^ Nat.find hex = 2 * 2 ^ (Nat.find hex - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h2]
    linarith

/-- **The covering of `ℝ`**: every real `ξ` lies in `[-1/4, 1/4]` or in one of the annuli. -/
theorem univ_subset_Icc_union_annulus :
    Set.univ ⊆ Set.Icc (-(1 / 4)) (1 / 4) ∪ ⋃ n, annulus n := fun ξ _ => by
  rcases le_or_gt |ξ| (1 / 4) with h | h
  · exact Or.inl (abs_le.1 h)
  · exact Or.inr (Set.mem_iUnion.2 (exists_mem_annulus h))

/-- **Integrability from geometric decay on the annuli**: a continuous `f : ℝ → E` with
`∫_{A_n} ‖f‖ ≤ M r^n` for every `n`, where `0 ≤ r < 1`, is integrable on `ℝ`. On `[-1/4, 1/4]` it
is integrable as a continuous function on a compact interval, on `⋃_n A_n` because the integrals
over the annuli are summable (Mathlib's `integrableOn_iUnion_of_summable_integral_norm`), and
these two sets cover `ℝ`. -/
theorem integrable_of_integral_annulus_le {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) {M r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ n : ℕ, ∫ ξ in annulus n, ‖f ξ‖ ≤ M * r ^ n) : Integrable f := by
  have h1 : IntegrableOn f (Set.Icc (-(1 / 4)) (1 / 4)) := hf.integrableOn_Icc
  have h2 : IntegrableOn f (⋃ n, annulus n) :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun n => hf.integrableOn_Icc.mono_set (annulus_subset_Icc n))
      (Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) h
        ((summable_geometric_of_lt_one hr0 hr1).mul_left M))
  exact integrableOn_univ.1 ((h1.union h2).mono_set univ_subset_Icc_union_annulus)

/-! ### The symbol product on the annuli -/

/-- `|sinc x| ≤ 1/|x|` for `x ≠ 0`, since `sinc x = sin x / x` and `|sin x| ≤ 1`. Mathlib's
`Real.sinc_le_inv_abs` is the one-sided bound `sinc x ≤ 1/|x|`. -/
theorem abs_sinc_le_inv_abs {x : ℝ} (hx : x ≠ 0) : |Real.sinc x| ≤ |x|⁻¹ := by
  rw [Real.sinc_of_ne_zero hx, abs_div, div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.2 (abs_nonneg x)) (Real.abs_sin_le_one x)

/-- On the annulus `A_n`: `sinc(πξ)^(2N) ≤ (4/(π 2^n))^(2N)`, since `|sinc(πξ)| ≤ 1/(π|ξ|)` and
`π|ξ| > π 2^n/4`. -/
theorem sinc_pow_le_of_mem_annulus (N : ℕ) {n : ℕ} {ξ : ℝ} (hξ : ξ ∈ annulus n) :
    Real.sinc (π * ξ) ^ (2 * N) ≤ (4 / (π * 2 ^ n)) ^ (2 * N) := by
  have hξ0 : 0 < |ξ| := lt_of_le_of_lt (by positivity) hξ.1
  have h1 : |Real.sinc (π * ξ)| ≤ 4 / (π * 2 ^ n) := by
    refine (abs_sinc_le_inv_abs (mul_ne_zero Real.pi_ne_zero (abs_pos.1 hξ0))).trans ?_
    rw [abs_mul, abs_of_pos Real.pi_pos]
    calc (π * |ξ|)⁻¹ ≤ (π * (2 ^ n / 4))⁻¹ := by
          gcongr
          exact hξ.1.le
      _ = 4 / (π * 2 ^ n) := by field_simp
  rw [← (even_two_mul N).pow_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 _

/-- **The pointwise bound on the annuli**: for `ξ ∈ A_n`,
`|Φ(ξ)|² ≤ exp(C(2N - 1, N) π²/12) (4/(π 2^n))^(2N) ∏_{j<n} P(ξ/2^(j+1))`, from
`Daubechies.normSq_symbolProduct_le` (`|ξ| ≤ 2^n/2` on `A_n`) and the bound on `sinc`
(`Daubechies.sinc_pow_le_of_mem_annulus`). -/
theorem normSq_symbolProduct_le_of_mem_annulus {N : ℕ} (m : Mask N) {n : ℕ} {ξ : ℝ}
    (hξ : ξ ∈ annulus n) :
    ‖symbolProduct m ξ‖ ^ 2 ≤ Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) *
      (4 / (π * 2 ^ n)) ^ (2 * N) * ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1)) := by
  refine (normSq_symbolProduct_le m hξ.2).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (sinc_pow_le_of_mem_annulus N hξ) (prod_daubFun_nonneg N n ξ)) (Real.exp_pos _).le

/-- **The integral of `|Φ|²` over an annulus**: under a growth bound `T^n 1 ≤ C λ^n`,
`∫_{A_n} |Φ(ξ)|² dξ ≤ exp(C(2N - 1, N) π²/12) (4/(π 2^n))^(2N) C λ^n` for every `n ∈ ℕ`. The
pointwise bound `Daubechies.normSq_symbolProduct_le_of_mem_annulus` leaves the integral of
`∏_{j<n} P(ξ/2^(j+1))` over `A_n ⊆ [-2^n/2, 2^n/2]`, which is at most `C λ^n`
(`Daubechies.TransferGrowth.setIntegral_prod_daubFun_le`). -/
theorem integral_annulus_normSq_le {N : ℕ} (m : Mask N) {lam C : ℝ}
    (hg : TransferGrowth N lam C) (n : ℕ) :
    ∫ ξ in annulus n, ‖symbolProduct m ξ‖ ^ 2 ≤
      Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) * (4 / (π * 2 ^ n)) ^ (2 * N) *
        (C * lam ^ n) := by
  have hc : Continuous fun ξ => ‖symbolProduct m ξ‖ ^ 2 :=
    (continuous_symbolProduct m).norm.pow 2
  have hK : 0 ≤ Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) *
      (4 / (π * 2 ^ n)) ^ (2 * N) := by positivity
  calc ∫ ξ in annulus n, ‖symbolProduct m ξ‖ ^ 2
      ≤ ∫ ξ in annulus n, Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) *
          (4 / (π * 2 ^ n)) ^ (2 * N) * ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1)) :=
        setIntegral_mono_on (hc.integrableOn_Icc.mono_set (annulus_subset_Icc n))
          ((continuous_const.mul (continuous_prod_daubFun N n)).integrableOn_Icc.mono_set
            (annulus_subset_Icc n))
          (measurableSet_annulus n) fun ξ hξ => normSq_symbolProduct_le_of_mem_annulus m hξ
    _ = Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) * (4 / (π * 2 ^ n)) ^ (2 * N) *
          ∫ ξ in annulus n, ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1)) :=
        integral_const_mul _ _
    _ ≤ Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) * (4 / (π * 2 ^ n)) ^ (2 * N) *
          (C * lam ^ n) :=
        mul_le_mul_of_nonneg_left (hg.setIntegral_prod_daubFun_le n (annulus_subset_Icc n)) hK

/-! ### Weights -/

/-- The weight `ξ ↦ (1 + |ξ|)^t` is continuous for every real `t`, since `1 + |ξ| > 0`. -/
theorem continuous_one_add_abs_rpow (t : ℝ) : Continuous fun ξ : ℝ => (1 + |ξ|) ^ t :=
  (continuous_const.add continuous_abs).rpow_const fun ξ =>
    Or.inl (by positivity : (0 : ℝ) < 1 + |ξ|).ne'

/-- **Comparable bases give comparable powers**: if `y > 0` and `y/4 ≤ x ≤ 4y`, then
`x^t ≤ 4^|t| y^t` for every real exponent `t` (for `t ≥ 0` from `x ≤ 4y`, for `t ≤ 0` from
`y/4 ≤ x`). -/
theorem rpow_le_four_rpow_abs_mul {x y t : ℝ} (hy : 0 < y) (h1 : y / 4 ≤ x) (h2 : x ≤ 4 * y) :
    x ^ t ≤ 4 ^ |t| * y ^ t := by
  have hx : 0 < x := lt_of_lt_of_le (by positivity) h1
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, ← Real.mul_rpow (by norm_num) hy.le]
    exact Real.rpow_le_rpow hx.le h2 ht
  · rw [abs_of_nonpos ht, Real.rpow_neg (by norm_num), ← div_eq_inv_mul,
      ← Real.div_rpow hy.le (by norm_num)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 ht

/-- **The weight on the annuli**: for `ξ ∈ A_n` and every real `t`,
`(1 + |ξ|)^t ≤ 4^|t| (2^t)^n`, since `2^n/4 ≤ 1 + |ξ| ≤ 4 · 2^n`
(`Daubechies.rpow_le_four_rpow_abs_mul`). -/
theorem one_add_abs_rpow_le_of_mem_annulus (t : ℝ) {n : ℕ} {ξ : ℝ} (hξ : ξ ∈ annulus n) :
    (1 + |ξ|) ^ t ≤ 4 ^ |t| * ((2 : ℝ) ^ t) ^ n := by
  rw [Real.rpow_pow_comm (by norm_num)]
  have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  refine rpow_le_four_rpow_abs_mul (by positivity) ?_ ?_
  · linarith [hξ.1]
  · linarith [hξ.2]

/-- `(4/(π 2^n))^(2N) = (4/π)^(2N) / (4^N)^n`, since `(2^n)^(2N) = 2^(2Nn) = (4^N)^n`. -/
theorem four_div_pi_mul_two_pow_pow (N n : ℕ) :
    (4 / (π * 2 ^ n)) ^ (2 * N) = (4 / π) ^ (2 * N) / ((4 : ℝ) ^ N) ^ n := by
  have h : ((2 : ℝ) ^ n) ^ (2 * N) = ((4 : ℝ) ^ N) ^ n := by
    rw [← pow_mul, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring
  rw [div_mul_eq_div_div, div_pow, h]

/-- `x^a c ≤ x^(2(a - b)) + x^(2b) c²` for `x > 0`, `c ≥ 0` and all real `a`, `b`: with
`u = x^(a - b)` and `v = x^b c`, `x^a c = uv ≤ 2uv ≤ u² + v²`. -/
theorem rpow_mul_le_rpow_add_rpow_mul_sq {x c : ℝ} (hx : 0 < x) (hc : 0 ≤ c) (a b : ℝ) :
    x ^ a * c ≤ x ^ (2 * (a - b)) + x ^ (2 * b) * c ^ 2 := by
  have h1 : x ^ a * c = x ^ (a - b) * (x ^ b * c) := by
    rw [← mul_assoc, ← Real.rpow_add hx, sub_add_cancel]
  have h2 : x ^ (2 * (a - b)) = (x ^ (a - b)) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hx.le, Real.rpow_two]
  have h3 : x ^ (2 * b) * c ^ 2 = (x ^ b * c) ^ 2 := by
    rw [mul_pow, mul_comm 2 b, Real.rpow_mul hx.le, Real.rpow_two]
  rw [h1, h2, h3]
  have hu : 0 ≤ x ^ (a - b) := by positivity
  have hv : 0 ≤ x ^ b * c := by positivity
  nlinarith [two_mul_le_add_sq (x ^ (a - b)) (x ^ b * c), mul_nonneg hu hv]

/-! ### Decay of the symbol product -/

/-- **The weighted `L²` bound on the symbol product**: under a growth bound `T^n 1 ≤ C λ^n`, the
function `ξ ↦ (1 + |ξ|)^(2s) |Φ(ξ)|²` is integrable for every real `s < N - log₄ λ`. On the
annulus `A_n` the weight is at most `4^|2s| 2^(2sn)`
(`Daubechies.one_add_abs_rpow_le_of_mem_annulus`) and
`∫_{A_n} |Φ|² ≤ exp(C(2N - 1, N) π²/12) (4/π)^(2N) C (λ/4^N)^n`
(`Daubechies.integral_annulus_normSq_le`), so the integrals over the annuli decay geometrically
with ratio `2^(2s) λ/4^N < 1` (`Daubechies.two_rpow_two_mul_mul_lt`,
`Daubechies.integrable_of_integral_annulus_le`). -/
theorem integrable_rpow_mul_normSq {N : ℕ} (m : Mask N) {lam C s : ℝ}
    (hg : TransferGrowth N lam C) (hs : s < N - Real.logb 4 lam) :
    Integrable (fun ξ => (1 + |ξ|) ^ (2 * s) * ‖symbolProduct m ξ‖ ^ 2) := by
  have hc : Continuous fun ξ => ‖symbolProduct m ξ‖ ^ 2 :=
    (continuous_symbolProduct m).norm.pow 2
  have hw := continuous_one_add_abs_rpow (2 * s)
  have hr : (2 : ℝ) ^ (2 * s) * lam / 4 ^ N < 1 := by
    rw [div_lt_one (by positivity)]
    exact two_rpow_two_mul_mul_lt hg.1 hs
  have hr0 : 0 ≤ (2 : ℝ) ^ (2 * s) * lam / 4 ^ N :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg zero_le_two _) hg.1.le) (by positivity)
  refine integrable_of_integral_annulus_le (hw.mul hc)
    (M := 4 ^ |2 * s| * (Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) *
      (4 / π) ^ (2 * N) * C)) hr0 hr fun n => ?_
  calc ∫ ξ in annulus n, ‖(1 + |ξ|) ^ (2 * s) * ‖symbolProduct m ξ‖ ^ 2‖
      = ∫ ξ in annulus n, (1 + |ξ|) ^ (2 * s) * ‖symbolProduct m ξ‖ ^ 2 := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        exact Real.norm_of_nonneg (by positivity)
    _ ≤ ∫ ξ in annulus n, 4 ^ |2 * s| * ((2 : ℝ) ^ (2 * s)) ^ n * ‖symbolProduct m ξ‖ ^ 2 :=
        setIntegral_mono_on ((hw.mul hc).integrableOn_Icc.mono_set (annulus_subset_Icc n))
          ((continuous_const.mul hc).integrableOn_Icc.mono_set (annulus_subset_Icc n))
          (measurableSet_annulus n) fun ξ hξ => mul_le_mul_of_nonneg_right
            (one_add_abs_rpow_le_of_mem_annulus _ hξ) (sq_nonneg _)
    _ = 4 ^ |2 * s| * ((2 : ℝ) ^ (2 * s)) ^ n * ∫ ξ in annulus n, ‖symbolProduct m ξ‖ ^ 2 :=
        integral_const_mul _ _
    _ ≤ 4 ^ |2 * s| * ((2 : ℝ) ^ (2 * s)) ^ n *
          (Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) * (4 / (π * 2 ^ n)) ^ (2 * N) *
            (C * lam ^ n)) :=
        mul_le_mul_of_nonneg_left (integral_annulus_normSq_le m hg n) (by positivity)
    _ = 4 ^ |2 * s| * (Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) *
          (4 / π) ^ (2 * N) * C) * ((2 : ℝ) ^ (2 * s) * lam / 4 ^ N) ^ n := by
        rw [four_div_pi_mul_two_pow_pow, div_pow ((2 : ℝ) ^ (2 * s) * lam), mul_pow]
        ring

/-- **The weighted `L¹` bound on the symbol product**: under a growth bound `T^n 1 ≤ C λ^n`, the
function `ξ ↦ (1 + |ξ|)^a |Φ(ξ)|` is integrable for every real `a < N - log₄ λ - 1/2`. Choose `b`
with `a + 1/2 < b < N - log₄ λ`; then
`(1 + |ξ|)^a |Φ(ξ)| ≤ (1 + |ξ|)^(-2(b - a)) + (1 + |ξ|)^(2b) |Φ(ξ)|²`
(`Daubechies.rpow_mul_le_rpow_add_rpow_mul_sq`), where the first summand is integrable since
`2(b - a) > 1` (Mathlib's `integrable_one_add_norm`) and the second by
`Daubechies.integrable_rpow_mul_normSq`. -/
theorem integrable_rpow_mul_norm {N : ℕ} (m : Mask N) {lam C a : ℝ}
    (hg : TransferGrowth N lam C) (ha : a < N - Real.logb 4 lam - 1 / 2) :
    Integrable (fun ξ => (1 + |ξ|) ^ a * ‖symbolProduct m ξ‖) := by
  obtain ⟨b, hb1, hb2⟩ : ∃ b : ℝ, b < N - Real.logb 4 lam ∧ 1 < 2 * (b - a) :=
    ⟨(a + 1 / 2 + (N - Real.logb 4 lam)) / 2, by linarith, by linarith⟩
  have h1 := integrable_rpow_mul_normSq m hg hb1
  have h2 : Integrable (fun ξ : ℝ => (1 + ‖ξ‖) ^ (-(2 * (b - a)))) :=
    integrable_one_add_norm (by simpa using hb2)
  have hc : Continuous fun ξ => (1 + |ξ|) ^ a * ‖symbolProduct m ξ‖ :=
    (continuous_one_add_abs_rpow a).mul (continuous_symbolProduct m).norm
  refine (h2.add h1).mono' hc.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity), Pi.add_apply, Real.norm_eq_abs,
    show -(2 * (b - a)) = 2 * (a - b) by ring]
  exact rpow_mul_le_rpow_add_rpow_mul_sq (by positivity) (norm_nonneg _) a b

/-- **The symbol product is integrable under a growth bound**: if `T^n 1 ≤ C λ^n`
(`Daubechies.TransferGrowth`) and `N - log₄ λ - 1/2 > 0`, then `Φ` is integrable. This is the case
`a = 0` of the weighted bound `Daubechies.integrable_rpow_mul_norm`. -/
theorem integrable_symbolProduct_of_growth {N : ℕ} (m : Mask N) {lam C : ℝ}
    (hg : TransferGrowth N lam C) (hpos : 0 < N - Real.logb 4 lam - 1 / 2) :
    Integrable (symbolProduct m) := by
  have h := integrable_rpow_mul_norm m hg (a := 0) hpos
  simp only [Real.rpow_zero, one_mul] at h
  exact (integrable_norm_iff (continuous_symbolProduct m).aestronglyMeasurable).1 h

/-- **The symbol product is integrable** for every Daubechies mask of order `N ≥ 2`: the crude
growth bound `T^n 1 ≤ (2 C(2N - 1, N))^n` (`Daubechies.transferGrowth_crude`) satisfies
`log₄(2 C(2N - 1, N)) < N - 1/2` (`Daubechies.logb_four_two_mul_choose_lt`), so
`Daubechies.integrable_symbolProduct_of_growth` applies. -/
theorem integrable_symbolProduct {N : ℕ} (m : Mask N) (hN : 2 ≤ N) :
    Integrable (symbolProduct m) :=
  integrable_symbolProduct_of_growth m (transferGrowth_crude N)
    (by linarith [logb_four_two_mul_choose_lt hN])

/-- **The symbol product is square integrable** for every Daubechies mask of order `N ≥ 2`: the
case `s = 0` of `Daubechies.integrable_rpow_mul_normSq` with the crude growth bound, since
`log₄(2 C(2N - 1, N)) < N - 1/2 < N`. -/
theorem memLp_symbolProduct_two {N : ℕ} (m : Mask N) (hN : 2 ≤ N) :
    MemLp (symbolProduct m) 2 := by
  have h := integrable_rpow_mul_normSq m (transferGrowth_crude N) (s := 0)
    (by linarith [logb_four_two_mul_choose_lt hN])
  simp only [mul_zero, Real.rpow_zero, one_mul] at h
  exact (memLp_two_iff_integrable_sq_norm (continuous_symbolProduct m).aestronglyMeasurable).2 h

end Daubechies

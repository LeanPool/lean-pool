/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Mask
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Field
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The symbol product

For a Daubechies mask of order `N` with symbol `m_0` (`Daubechies.symbol`) the
**symbol product** is the infinite product

`Φ(ξ) = ∏_{j ≥ 0} m_0(ξ/2^(j+1))` (`Daubechies.symbolProduct`).

The scaling function of the mask is the inverse Fourier transform of `Φ`.

**Convergence.** Since `|m_0(η) - 1| ≤ C|η|` (`Daubechies.norm_symbol_sub_one_le`), the factors
satisfy `|m_0(ξ/2^(j+1)) - 1| ≤ C|ξ|/2^(j+1)`, a summable bound, uniform for `ξ` in a compact
set. Hence the product converges for every `ξ` (`Daubechies.multipliable_symbolProduct`, from
Mathlib's `multipliable_one_add_of_summable`), uniformly on compact sets
(`Daubechies.hasProdUniformlyOn_symbolProduct`), the partial products
`∏_{j<n} m_0(ξ/2^(j+1))` converge to `Φ(ξ)` for every `ξ` (`Daubechies.tendsto_prod_symbol`) and
locally uniformly in `ξ` (`Daubechies.tendstoLocallyUniformly_prod_symbol`), and `Φ` is
continuous (`Daubechies.continuous_symbolProduct`).

**Algebraic properties.** `Φ(0) = 1` (`Daubechies.symbolProduct_zero`), `|Φ(ξ)| ≤ 1` since
`|m_0| ≤ 1` (`Daubechies.norm_symbolProduct_le_one`), `Φ(-ξ) = conj Φ(ξ)`
(`Daubechies.symbolProduct_neg`), and `Φ(ξ) = ∏_{j<n} m_0(ξ/2^(j+1)) · Φ(ξ/2^n)` for every `n`
(`Daubechies.symbolProduct_eq_prod_mul`), in particular the refinement identity
`Φ(2ξ) = m_0(ξ) Φ(ξ)` (`Daubechies.symbolProduct_two_mul`); the partial products
`p_n(ξ) = ∏_{j<n} m_0(ξ/2^(j+1))` satisfy `p_{n+1}(ξ) = m_0(ξ/2) p_n(ξ/2)`
(`Daubechies.prod_range_succ_symbol`). For `|ξ| ≤ 1/2` every argument
`ξ/2^(j+1)` lies in `[-1/4, 1/4]`, where `m_0` has no zeros, so `Φ(ξ) ≠ 0`
(`Daubechies.symbolProduct_ne_zero`, from Mathlib's `tprod_one_add_ne_zero_of_summable`), and by
compactness `|Φ| ≥ κ > 0` on `[-1/2, 1/2]` (`Daubechies.exists_pos_le_norm_symbolProduct`).

**The modulus.** The cosine product `∏_{j ≥ 0} cos(x/2^(j+1)) = sinc x` (`Daubechies.tprod_cos`)
follows from the identity `sinc(x/2^n) ∏_{j<n} cos(x/2^(j+1)) = sinc x`
(`Daubechies.sinc_div_two_pow_mul_prod_cos`, from `sin 2y = 2 sin y cos y`) and
`sinc(x/2^n) → sinc 0 = 1`. Together with `|m_0(η)|² = cos(πη)^(2N) P(η)`, where
`P(η) = P_N(sin²(πη))` (`Daubechies.daubFun`), it gives

`|Φ(ξ)|² = sinc(πξ)^(2N) ∏_{j ≥ 0} P(ξ/2^(j+1))` (`Daubechies.normSq_symbolProduct`).

The real product converges since `0 ≤ P(η) - 1 ≤ C(2N - 1, N) π² η²` for `N ≥ 1`, and since
`P = 0` for `N = 0` (`Daubechies.multipliable_daubFun`), and it splits into the first `n` factors
and the tail `∏_{j ≥ 0} P(ξ/2^(n+j+1))` (`Daubechies.tprod_daubFun_eq_prod_mul`). With
`1 + t ≤ e^t` and `∑_{j ≥ 0} (x/2^(j+1))² = x²/3` (`Daubechies.hasSum_sq_div_two_pow`),
`∏_{j ≥ 0} P(x/2^(j+1)) ≤ exp(C(2N - 1, N) π² x²/3)` (`Daubechies.tprod_daubFun_le`), so for
`|ξ| ≤ 2^n/2` the tail is at most `exp(C(2N - 1, N) π²/12)`
(`Daubechies.tprod_daubFun_shift_le`) and
`|Φ(ξ)|² ≤ exp(C(2N - 1, N) π²/12) sinc(πξ)^(2N) ∏_{j<n} P(ξ/2^(j+1))`
(`Daubechies.normSq_symbolProduct_le`).
-/

@[expose] public section

open Filter Topology
open scoped Real ComplexConjugate

namespace Daubechies

/-! ### Dyadic scalings -/

/-- `ξ/2^(n+j+1) = (ξ/2^n)/2^(j+1)`: the arguments of the tail of a dyadic product are the
arguments of the full product at the point `ξ/2^n`. -/
theorem div_two_pow_add_succ (ξ : ℝ) (n j : ℕ) :
    ξ / 2 ^ (n + j + 1) = ξ / 2 ^ n / 2 ^ (j + 1) := by
  rw [div_div, ← pow_add, add_assoc]

/-- `(x/2^(j+1))² = (x²/4) (1/4)^j` for every real `x` and every `j ∈ ℕ`. -/
theorem sq_div_two_pow_succ (x : ℝ) (j : ℕ) :
    (x / 2 ^ (j + 1)) ^ 2 = x ^ 2 / 4 * (1 / 4) ^ j := by
  rw [div_pow, ← pow_mul, mul_comm (j + 1) 2, pow_mul, one_div_pow, pow_succ]
  norm_num
  ring

/-- **The geometric series of the squared dyadic scalings**:
`∑_{j ≥ 0} (x/2^(j+1))² = x² ∑_{j ≥ 0} 4^(-(j+1)) = x²/3`. -/
theorem hasSum_sq_div_two_pow (x : ℝ) :
    HasSum (fun j : ℕ => (x / 2 ^ (j + 1)) ^ 2) (x ^ 2 / 3) := by
  have h := (hasSum_geometric_of_lt_one (r := 1 / 4) (by norm_num) (by norm_num)).mul_left
    (x ^ 2 / 4)
  convert h using 1
  · exact funext fun j => sq_div_two_pow_succ x j
  · norm_num
    ring

/-! ### The cosine product -/

/-- **The doubling formula for `sinc`**: `sinc(y) cos(y) = sinc(2y)` for every real `y`, from
`sin(2y) = 2 sin(y) cos(y)` (Mathlib's `Real.sin_two_mul`); at `y = 0` both sides are `1`. -/
theorem sinc_mul_cos (y : ℝ) : Real.sinc y * Real.cos y = Real.sinc (2 * y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [Real.sinc_of_ne_zero hy, Real.sinc_of_ne_zero (mul_ne_zero two_ne_zero hy),
      Real.sin_two_mul]
    field_simp

/-- **The finite cosine product**: `sinc(x/2^n) ∏_{j<n} cos(x/2^(j+1)) = sinc(x)` for every real
`x` and every `n ∈ ℕ`, by induction on `n` with `sinc(y) cos(y) = sinc(2y)` at
`y = x/2^(n+1)`. -/
theorem sinc_div_two_pow_mul_prod_cos (x : ℝ) (n : ℕ) :
    Real.sinc (x / 2 ^ n) * ∏ j ∈ Finset.range n, Real.cos (x / 2 ^ (j + 1)) = Real.sinc x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : 2 * (x / 2 ^ (n + 1)) = x / 2 ^ n := by
      rw [pow_succ]
      field_simp
    calc Real.sinc (x / 2 ^ (n + 1)) * ∏ j ∈ Finset.range (n + 1), Real.cos (x / 2 ^ (j + 1))
        = Real.sinc (x / 2 ^ (n + 1)) * Real.cos (x / 2 ^ (n + 1)) *
            ∏ j ∈ Finset.range n, Real.cos (x / 2 ^ (j + 1)) := by
          rw [Finset.prod_range_succ]
          ring
      _ = Real.sinc x := by rw [sinc_mul_cos, h2, ih]

/-- `|cos(y) - 1| ≤ y²/2` for every real `y`, from `1 - y²/2 ≤ cos(y) ≤ 1` (Mathlib's
`Real.one_sub_sq_div_two_le_cos`). -/
theorem norm_cos_sub_one_le (y : ℝ) : ‖Real.cos y - 1‖ ≤ y ^ 2 / 2 := by
  rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Real.cos_le_one y))]
  linarith [Real.one_sub_sq_div_two_le_cos (x := y)]

/-- The infinite product `∏_{j ≥ 0} cos(x/2^(j+1))` converges: its factors are `1 + a_j` with
`|a_j| ≤ (x/2^(j+1))²/2`, a summable bound (Mathlib's `Real.multipliable_one_add_of_summable`). -/
theorem multipliable_cos_div_two_pow (x : ℝ) :
    Multipliable (fun j : ℕ => Real.cos (x / 2 ^ (j + 1))) := by
  have hs : Summable (fun j : ℕ => Real.cos (x / 2 ^ (j + 1)) - 1) :=
    Summable.of_norm_bounded ((hasSum_sq_div_two_pow x).summable.div_const 2)
      fun _ => norm_cos_sub_one_le _
  simpa only [add_sub_cancel] using Real.multipliable_one_add_of_summable hs

/-- **The cosine product as a `HasProd`**: `∏_{j ≥ 0} cos(x/2^(j+1)) = sinc(x)`. The partial
products `p_n` satisfy `sinc(x/2^n) p_n = sinc(x)`
(`Daubechies.sinc_div_two_pow_mul_prod_cos`); since `sinc(x/2^n) → sinc(0) = 1` and `p_n`
converges, the limit of `p_n` is `sinc(x)`. -/
theorem hasProd_cos_div_two_pow (x : ℝ) :
    HasProd (fun j : ℕ => Real.cos (x / 2 ^ (j + 1))) (Real.sinc x) := by
  have hm := multipliable_cos_div_two_pow x
  have h0 : Tendsto (fun n : ℕ => x / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have h1 : Tendsto (fun n : ℕ => Real.sinc (x / 2 ^ n)) atTop (𝓝 1) := by
    simpa [Function.comp_def, Real.sinc_zero] using (Real.continuous_sinc.tendsto 0).comp h0
  have h2 := hm.tendsto_prod_tprod_nat
  have h3 := h1.mul h2
  simp only [sinc_div_two_pow_mul_prod_cos, one_mul] at h3
  have h4 : Real.sinc x = ∏' j : ℕ, Real.cos (x / 2 ^ (j + 1)) :=
    tendsto_nhds_unique tendsto_const_nhds h3
  rw [h4]
  exact hm.hasProd

/-- **The cosine product**: `∏_{j ≥ 0} cos(x/2^(j+1)) = sinc(x)` for every real `x`, where
`sinc(x) = sin(x)/x` for `x ≠ 0` and `sinc(0) = 1`. -/
theorem tprod_cos (x : ℝ) : ∏' j : ℕ, Real.cos (x / 2 ^ (j + 1)) = Real.sinc x :=
  (hasProd_cos_div_two_pow x).tprod_eq

/-! ### The real product of the trigonometric Daubechies polynomial -/

/-- **The product of the trigonometric Daubechies polynomial converges**:
`∏_{j ≥ 0} P(x/2^(j+1))` is multipliable for every `N` and every real `x`, where
`P = Daubechies.daubFun N`. For `N ≥ 1` the factors are `1 + a_j` with
`0 ≤ a_j ≤ C(2N - 1, N) π² (x/2^(j+1))²` (`Daubechies.one_le_daubFun`, `Daubechies.daubFun_le`),
a summable bound; for `N = 0` every factor is `0`. -/
theorem multipliable_daubFun (N : ℕ) (x : ℝ) :
    Multipliable (fun j : ℕ => daubFun N (x / 2 ^ (j + 1))) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact multipliable_of_exists_eq_zero ⟨0, by simp [daubFun, daubPoly_zero]⟩
  · have hs : Summable (fun j : ℕ => daubFun N (x / 2 ^ (j + 1)) - 1) := by
      refine Summable.of_nonneg_of_le (fun _ => sub_nonneg.2 (one_le_daubFun hN _))
        (fun j => ?_) ((hasSum_sq_div_two_pow x).summable.mul_left
          (((2 * N - 1).choose N : ℝ) * π ^ 2))
      have := daubFun_le N (x / 2 ^ (j + 1))
      linarith
    simpa only [add_sub_cancel] using Real.multipliable_one_add_of_summable hs

/-- The tail `∏_{j ≥ 0} P(ξ/2^(n+j+1))` of the product of the trigonometric Daubechies
polynomial converges: it is the full product at the point `ξ/2^n`. -/
theorem multipliable_daubFun_shift (N n : ℕ) (ξ : ℝ) :
    Multipliable (fun j : ℕ => daubFun N (ξ / 2 ^ (n + j + 1))) := by
  simpa only [div_two_pow_add_succ] using multipliable_daubFun N (ξ / 2 ^ n)

/-- The product of the trigonometric Daubechies polynomial is nonnegative:
`∏_{j ≥ 0} P(x/2^(j+1)) ≥ 0` for every `N` and every real `x`, since `P ≥ 0`
(`Daubechies.daubFun_nonneg`, Mathlib's `tprod_nonneg`). -/
theorem tprod_daubFun_nonneg (N : ℕ) (x : ℝ) : 0 ≤ ∏' j : ℕ, daubFun N (x / 2 ^ (j + 1)) :=
  tprod_nonneg fun _ => daubFun_nonneg N _

/-- **The split into the first `n` factors and the tail**:
`∏_{j ≥ 0} P(ξ/2^(j+1)) = ∏_{j<n} P(ξ/2^(j+1)) · ∏_{j ≥ 0} P(ξ/2^(n+j+1))` for every `n`
(Mathlib's `Multipliable.prod_mul_tprod_nat_mul'`, which needs the tail to converge). -/
theorem tprod_daubFun_eq_prod_mul (N n : ℕ) (ξ : ℝ) :
    ∏' j : ℕ, daubFun N (ξ / 2 ^ (j + 1)) =
      (∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1))) *
        ∏' j : ℕ, daubFun N (ξ / 2 ^ (n + j + 1)) := by
  have hm : Multipliable (fun j : ℕ => daubFun N (ξ / 2 ^ (j + n + 1))) := by
    simpa only [add_comm _ n] using multipliable_daubFun_shift N n ξ
  rw [← Multipliable.prod_mul_tprod_nat_mul' (f := fun j : ℕ => daubFun N (ξ / 2 ^ (j + 1))) hm]
  simp only [add_comm _ n]

/-- **The bound on the product of the trigonometric Daubechies polynomial**:
`∏_{j ≥ 0} P(x/2^(j+1)) ≤ exp(C(2N - 1, N) π² x²/3)` for every `N` and every real `x`. Each
factor is at most `1 + C(2N - 1, N) π² (x/2^(j+1))² ≤ exp(C(2N - 1, N) π² (x/2^(j+1))²)`
(`Daubechies.daubFun_le`, Mathlib's `Real.prod_one_add_le_exp_sum`), and
`∑_{j ≥ 0} (x/2^(j+1))² = x²/3`. -/
theorem tprod_daubFun_le (N : ℕ) (x : ℝ) :
    ∏' j : ℕ, daubFun N (x / 2 ^ (j + 1)) ≤
      Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 * (x ^ 2 / 3)) := by
  refine (multipliable_daubFun N x).tprod_le_of_prod_range_le fun k => ?_
  calc ∏ j ∈ Finset.range k, daubFun N (x / 2 ^ (j + 1))
      ≤ ∏ j ∈ Finset.range k,
          (1 + ((2 * N - 1).choose N : ℝ) * π ^ 2 * (x / 2 ^ (j + 1)) ^ 2) :=
        Finset.prod_le_prod₀ (fun _ _ => daubFun_nonneg N _) (fun _ _ => daubFun_le N _)
    _ ≤ Real.exp (∑ j ∈ Finset.range k,
          ((2 * N - 1).choose N : ℝ) * π ^ 2 * (x / 2 ^ (j + 1)) ^ 2) :=
        Real.prod_one_add_le_exp_sum _ fun _ => by positivity
    _ ≤ Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 * (x ^ 2 / 3)) := by
        rw [← Finset.mul_sum]
        gcongr
        exact sum_le_hasSum _ (fun _ _ => sq_nonneg _) (hasSum_sq_div_two_pow x)

/-- **The tail bound**: for `|ξ| ≤ 2^n/2`,
`∏_{j ≥ 0} P(ξ/2^(n+j+1)) ≤ exp(C(2N - 1, N) π²/12)`. The tail is the full product at
`x = ξ/2^n`, and `|x| ≤ 1/2` gives `x²/3 ≤ 1/12` in `Daubechies.tprod_daubFun_le`. -/
theorem tprod_daubFun_shift_le (N : ℕ) {n : ℕ} {ξ : ℝ} (h : |ξ| ≤ 2 ^ n / 2) :
    ∏' j : ℕ, daubFun N (ξ / 2 ^ (n + j + 1)) ≤
      Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) := by
  simp only [div_two_pow_add_succ]
  refine (tprod_daubFun_le N (ξ / 2 ^ n)).trans (Real.exp_le_exp.2 ?_)
  have h1 : |ξ / 2 ^ n| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n), div_le_iff₀ (by positivity)]
    linarith
  have hx : (ξ / 2 ^ n) ^ 2 ≤ 1 / 4 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at this
    linarith
  have hC : 0 ≤ ((2 * N - 1).choose N : ℝ) * π ^ 2 := by positivity
  calc ((2 * N - 1).choose N : ℝ) * π ^ 2 * ((ξ / 2 ^ n) ^ 2 / 3)
      ≤ ((2 * N - 1).choose N : ℝ) * π ^ 2 * (1 / 4 / 3) := by gcongr
    _ = ((2 * N - 1).choose N : ℝ) * π ^ 2 / 12 := by ring

/-! ### The symbol product: convergence and continuity -/

variable {N : ℕ} (m : Mask N)

/-- **The symbol product** of a mask: `Φ(ξ) = ∏_{j ≥ 0} m_0(ξ/2^(j+1))`, where `m_0` is the
symbol (`Daubechies.symbol`). The product converges for every `ξ`
(`Daubechies.multipliable_symbolProduct`). -/
noncomputable def symbolProduct (ξ : ℝ) : ℂ := ∏' j : ℕ, symbol m (ξ / 2 ^ (j + 1))

/-- `|m_0(ξ/2^(j+1)) - 1| ≤ (C|ξ|/2)/2^j` with `C = π ∑_k k |c_k|` (`Daubechies.symbolLip`), from
`|m_0(η) - 1| ≤ C|η|`. -/
theorem norm_symbol_div_two_pow_sub_one_le (ξ : ℝ) (j : ℕ) :
    ‖symbol m (ξ / 2 ^ (j + 1)) - 1‖ ≤ symbolLip m * |ξ| / 2 / 2 ^ j := by
  calc ‖symbol m (ξ / 2 ^ (j + 1)) - 1‖ ≤ symbolLip m * |ξ / 2 ^ (j + 1)| :=
        norm_symbol_sub_one_le m _
    _ = symbolLip m * |ξ| / 2 / 2 ^ j := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (j + 1)), pow_succ]
        ring

/-- The deviations `|m_0(ξ/2^(j+1)) - 1|` are summable over `j`: they are bounded by the
geometric sequence `(C|ξ|/2)/2^j`. -/
theorem summable_norm_symbol_sub_one (ξ : ℝ) :
    Summable (fun j : ℕ => ‖symbol m (ξ / 2 ^ (j + 1)) - 1‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_symbol_div_two_pow_sub_one_le m ξ)
    (summable_geometric_two' _)

/-- **The symbol product converges** for every `ξ`: the factors are `1 + a_j` with
`∑_j |a_j| < ∞` (Mathlib's `multipliable_one_add_of_summable`). -/
theorem multipliable_symbolProduct (ξ : ℝ) :
    Multipliable (fun j : ℕ => symbol m (ξ / 2 ^ (j + 1))) := by
  simpa only [add_sub_cancel] using
    multipliable_one_add_of_summable (summable_norm_symbol_sub_one m ξ)

/-- **Uniform convergence on compact sets**: on every compact set `K ⊆ ℝ`, say `K ⊆ [-R, R]`, the
symbol product converges uniformly, since there `|m_0(ξ/2^(j+1)) - 1| ≤ (CR/2)/2^j` (Mathlib's
`Summable.hasProdUniformlyOn_nat_one_add`). -/
theorem hasProdUniformlyOn_symbolProduct {K : Set ℝ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun j ξ => symbol m (ξ / 2 ^ (j + 1))) (symbolProduct m) K := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have h := Summable.hasProdUniformlyOn_nat_one_add (f := fun j ξ => symbol m (ξ / 2 ^ (j + 1)) - 1)
    hK (summable_geometric_two' (symbolLip m * R))
    (Eventually.of_forall fun j ξ hξ => (norm_symbol_div_two_pow_sub_one_le m ξ j).trans (by
      have := symbolLip_nonneg m
      have hξR : |ξ| ≤ R := hR ξ hξ
      gcongr))
    (fun _ => (((continuous_symbol m).comp (continuous_id.div_const _)).sub
      continuous_const).continuousOn)
  simp only [add_sub_cancel] at h
  exact h

/-- **Locally uniform convergence**: the products `∏_{j ∈ s} m_0(ξ/2^(j+1))` over finite sets
`s ⊆ ℕ` converge to `Φ(ξ)` as `s` grows, locally uniformly in `ξ ∈ ℝ`: uniformly on every compact
set (`Daubechies.hasProdUniformlyOn_symbolProduct`, Mathlib's
`hasProdLocallyUniformly_of_forall_compact`). -/
theorem hasProdLocallyUniformly_symbolProduct :
    HasProdLocallyUniformly (fun j ξ => symbol m (ξ / 2 ^ (j + 1))) (symbolProduct m) :=
  hasProdLocallyUniformly_of_forall_compact fun _ hK => hasProdUniformlyOn_symbolProduct m hK

/-- **The partial products converge locally uniformly**:
`∏_{j<n} m_0(ξ/2^(j+1)) → Φ(ξ)` as `n → ∞`, locally uniformly in `ξ ∈ ℝ`. -/
theorem tendstoLocallyUniformly_prod_symbol :
    TendstoLocallyUniformly (fun n ξ => ∏ j ∈ Finset.range n, symbol m (ξ / 2 ^ (j + 1)))
      (symbolProduct m) atTop :=
  (hasProdLocallyUniformly_symbolProduct m).tendstoLocallyUniformly_finsetRange

/-- **The partial products converge pointwise**: `∏_{j<n} m_0(ξ/2^(j+1)) → Φ(ξ)` as
`n → ∞`, for every `ξ`. -/
theorem tendsto_prod_symbol (ξ : ℝ) :
    Tendsto (fun n => ∏ j ∈ Finset.range n, symbol m (ξ / 2 ^ (j + 1))) atTop
      (𝓝 (symbolProduct m ξ)) :=
  (multipliable_symbolProduct m ξ).tendsto_prod_tprod_nat

/-- **The symbol product is continuous**, as a locally uniform limit of the continuous partial
products. -/
theorem continuous_symbolProduct : Continuous (symbolProduct m) :=
  (tendstoLocallyUniformly_prod_symbol m).continuous (Frequently.of_forall fun _ =>
    continuous_finsetProd _ fun _ _ => (continuous_symbol m).comp (continuous_id.div_const _))

/-! ### Algebraic properties of the symbol product -/

/-- `Φ(0) = 1`: every factor is `m_0(0) = 1`. -/
theorem symbolProduct_zero : symbolProduct m 0 = 1 := by
  simp [symbolProduct, symbol_zero]

/-- The partial products have modulus at most `1`:
`|∏_{j<n} m_0(ξ/2^(j+1))| ≤ 1`, since `|m_0| ≤ 1`. -/
theorem norm_prod_symbol_le_one (ξ : ℝ) (n : ℕ) :
    ‖∏ j ∈ Finset.range n, symbol m (ξ / 2 ^ (j + 1))‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_symbol_le_one m _

/-- **`|Φ| ≤ 1`**: the modulus of the product is the product of the moduli
(Mathlib's `Multipliable.norm_tprod`), whose partial products are at most `1`. -/
theorem norm_symbolProduct_le_one (ξ : ℝ) : ‖symbolProduct m ξ‖ ≤ 1 := by
  rw [symbolProduct, (multipliable_symbolProduct m ξ).norm_tprod]
  refine (multipliable_symbolProduct m ξ).norm.tprod_le_of_prod_range_le fun n => ?_
  rw [← norm_prod]
  exact norm_prod_symbol_le_one m ξ n

/-- **Splitting off the first factor of a partial product**:
`∏_{j<n+1} m_0(ξ/2^(j+1)) = m_0(ξ/2) ∏_{j<n} m_0((ξ/2)/2^(j+1))`, since
`ξ/2^(j+2) = (ξ/2)/2^(j+1)`. -/
theorem prod_range_succ_symbol (ξ : ℝ) (n : ℕ) :
    ∏ j ∈ Finset.range (n + 1), symbol m (ξ / 2 ^ (j + 1)) =
      symbol m (ξ / 2) * ∏ j ∈ Finset.range n, symbol m (ξ / 2 / 2 ^ (j + 1)) := by
  rw [Finset.prod_range_succ', zero_add, pow_one, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [div_div, ← pow_succ']

/-- **Splitting off the first `n` factors**:
`Φ(ξ) = ∏_{j<n} m_0(ξ/2^(j+1)) · Φ(ξ/2^n)` for every `n`, since
`ξ/2^(n+j+1) = (ξ/2^n)/2^(j+1)` (Mathlib's `Multipliable.prod_mul_tprod_nat_mul'`). -/
theorem symbolProduct_eq_prod_mul (ξ : ℝ) (n : ℕ) :
    symbolProduct m ξ =
      (∏ j ∈ Finset.range n, symbol m (ξ / 2 ^ (j + 1))) * symbolProduct m (ξ / 2 ^ n) := by
  have h : ∀ j : ℕ, ξ / 2 ^ (j + n + 1) = ξ / 2 ^ n / 2 ^ (j + 1) := fun j => by
    rw [add_comm j n]
    exact div_two_pow_add_succ ξ n j
  have hm : Multipliable (fun j : ℕ => symbol m (ξ / 2 ^ (j + n + 1))) := by
    simpa only [h] using multipliable_symbolProduct m (ξ / 2 ^ n)
  rw [symbolProduct, ← Multipliable.prod_mul_tprod_nat_mul'
    (f := fun j : ℕ => symbol m (ξ / 2 ^ (j + 1))) hm, symbolProduct]
  simp only [h]

/-- **The refinement identity** `Φ(2ξ) = m_0(ξ) Φ(ξ)`: the case `n = 1` of
`Daubechies.symbolProduct_eq_prod_mul` at the point `2ξ`. -/
theorem symbolProduct_two_mul (ξ : ℝ) :
    symbolProduct m (2 * ξ) = symbol m ξ * symbolProduct m ξ := by
  rw [symbolProduct_eq_prod_mul m (2 * ξ) 1, Finset.prod_range_one, zero_add, pow_one,
    mul_div_cancel_left₀ ξ two_ne_zero]

/-- **`Φ(-ξ) = conj Φ(ξ)`**: every factor satisfies `m_0(-η) = conj m_0(η)`
(`Daubechies.symbol_neg`), and complex conjugation is a continuous multiplicative map. -/
theorem symbolProduct_neg (ξ : ℝ) : symbolProduct m (-ξ) = conj (symbolProduct m ξ) := by
  have h := (multipliable_symbolProduct m ξ).hasProd.map (starRingEnd ℂ) Complex.continuous_conj
  rw [symbolProduct, symbolProduct, ← h.tprod_eq]
  congr 1
  funext j
  simp only [Function.comp_apply, neg_div, symbol_neg]

/-- **`Φ` has no zeros on `[-1/2, 1/2]`**: for `|ξ| ≤ 1/2` every argument `ξ/2^(j+1)` has modulus
`≤ 1/4 < 1/2`, so no factor vanishes (`Daubechies.symbol_ne_zero`), and a convergent product of
nonzero factors `1 + a_j` with `∑_j |a_j| < ∞` is nonzero (Mathlib's
`tprod_one_add_ne_zero_of_summable`). -/
theorem symbolProduct_ne_zero {ξ : ℝ} (h : |ξ| ≤ 1 / 2) : symbolProduct m ξ ≠ 0 := by
  have h1 : ∀ j : ℕ, 1 + (symbol m (ξ / 2 ^ (j + 1)) - 1) ≠ 0 := fun j => by
    rw [add_sub_cancel]
    apply symbol_ne_zero
    have h2 : (2 : ℝ) ≤ 2 ^ (j + 1) := le_self_pow₀ one_le_two (Nat.succ_ne_zero j)
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (j + 1)), div_lt_iff₀ (by positivity)]
    linarith
  have h3 := tprod_one_add_ne_zero_of_summable h1 (summable_norm_symbol_sub_one m ξ)
  simp only [add_sub_cancel] at h3
  exact h3

/-- **`|Φ|` is bounded below on `[-1/2, 1/2]`**: there is `κ > 0` with `κ ≤ |Φ(ξ)|` for all
`|ξ| ≤ 1/2`, namely the minimum of the continuous function `|Φ|` on the compact interval, which is
positive since `Φ` has no zeros there. -/
theorem exists_pos_le_norm_symbolProduct :
    ∃ κ > 0, ∀ ξ : ℝ, |ξ| ≤ 1 / 2 → κ ≤ ‖symbolProduct m ξ‖ := by
  obtain ⟨ξ₀, hξ₀, hmin⟩ := (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)).exists_isMinOn
    (Set.nonempty_Icc.2 (by norm_num)) (continuous_symbolProduct m).norm.continuousOn
  refine ⟨‖symbolProduct m ξ₀‖, norm_pos_iff.2 (symbolProduct_ne_zero m (abs_le.2 hξ₀)),
    fun ξ hξ => ?_⟩
  exact isMinOn_iff.1 hmin ξ (abs_le.1 hξ)

/-! ### The modulus of the symbol product -/

/-- **The squared modulus of the symbol product**:
`|Φ(ξ)|² = sinc(πξ)^(2N) ∏_{j ≥ 0} P(ξ/2^(j+1))`, where `P = Daubechies.daubFun N`. The factors
satisfy `|m_0(η)|² = cos(πη)^(2N) P(η)` (`Daubechies.normSq_symbol`), and
`∏_{j ≥ 0} cos(πξ/2^(j+1)) = sinc(πξ)` (`Daubechies.hasProd_cos_div_two_pow`); both products
converge, so the product of the squared moduli is the product of the two. -/
theorem normSq_symbolProduct (ξ : ℝ) :
    ‖symbolProduct m ξ‖ ^ 2 =
      Real.sinc (π * ξ) ^ (2 * N) * ∏' j : ℕ, daubFun N (ξ / 2 ^ (j + 1)) := by
  have h1 : HasProd (fun j : ℕ => ‖symbol m (ξ / 2 ^ (j + 1))‖ ^ 2) (‖symbolProduct m ξ‖ ^ 2) :=
    (multipliable_symbolProduct m ξ).hasProd.norm.pow 2
  have h2 : HasProd
      (fun j : ℕ => Real.cos (π * ξ / 2 ^ (j + 1)) ^ (2 * N) * daubFun N (ξ / 2 ^ (j + 1)))
      (Real.sinc (π * ξ) ^ (2 * N) * ∏' j : ℕ, daubFun N (ξ / 2 ^ (j + 1))) :=
    ((hasProd_cos_div_two_pow (π * ξ)).pow (2 * N)).mul (multipliable_daubFun N ξ).hasProd
  have h3 : (fun j : ℕ => ‖symbol m (ξ / 2 ^ (j + 1))‖ ^ 2) =
      fun j : ℕ => Real.cos (π * ξ / 2 ^ (j + 1)) ^ (2 * N) * daubFun N (ξ / 2 ^ (j + 1)) := by
    funext j
    rw [normSq_symbol, mul_div_assoc]
  rw [h3] at h1
  exact h1.unique h2

/-- **The bound on `|Φ|²` by a finite product**: for `|ξ| ≤ 2^n/2`,
`|Φ(ξ)|² ≤ exp(C(2N - 1, N) π²/12) · sinc(πξ)^(2N) ∏_{j<n} P(ξ/2^(j+1))`. The product of `P` splits
into the first `n` factors and the tail (`Daubechies.tprod_daubFun_eq_prod_mul`), and the tail is
at most `exp(C(2N - 1, N) π²/12)` (`Daubechies.tprod_daubFun_shift_le`). -/
theorem normSq_symbolProduct_le {n : ℕ} {ξ : ℝ} (h : |ξ| ≤ 2 ^ n / 2) :
    ‖symbolProduct m ξ‖ ^ 2 ≤ Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) *
      (Real.sinc (π * ξ) ^ (2 * N) * ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1))) := by
  rw [normSq_symbolProduct, tprod_daubFun_eq_prod_mul N n ξ]
  have h1 : 0 ≤ Real.sinc (π * ξ) ^ (2 * N) := (even_two_mul N).pow_nonneg _
  have h2 : 0 ≤ ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1)) :=
    Finset.prod_nonneg fun _ _ => daubFun_nonneg N _
  have h3 := tprod_daubFun_shift_le N h
  calc Real.sinc (π * ξ) ^ (2 * N) * ((∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1))) *
        ∏' j : ℕ, daubFun N (ξ / 2 ^ (n + j + 1)))
      = Real.sinc (π * ξ) ^ (2 * N) * (∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1))) *
          ∏' j : ℕ, daubFun N (ξ / 2 ^ (n + j + 1)) := by ring
    _ ≤ Real.sinc (π * ξ) ^ (2 * N) * (∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1))) *
          Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) := by gcongr
    _ = Real.exp (((2 * N - 1).choose N : ℝ) * π ^ 2 / 12) *
          (Real.sinc (π * ξ) ^ (2 * N) * ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1))) := by
        ring

end Daubechies

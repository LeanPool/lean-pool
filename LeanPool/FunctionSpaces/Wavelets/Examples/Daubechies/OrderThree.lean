/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Besov
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.MaskExistence

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Daubechies wavelets of order three

This file collects the regularity of the scaling function `φ` (`Daubechies.scalingFun`) of a
Daubechies mask of order `N = 3` and the characterisation of `B^s_{p,q}(ℝ)` by its coefficients.
All exponents come from the growth bound `T^n 1 ≤ 2 · 9^n` of the transfer operator
(`Daubechies.transferGrowth_three`), whose Sobolev exponent is
`3 - log₄ 9 = 3 - log₂ 3 ≈ 1.415` (`Daubechies.three_sub_logb_four_nine`). Masks of order three
exist (`Daubechies.exists_mask`), so every statement below applies to at least one mask
(`Daubechies.exists_mask_order_three_regular`). For every mask `m : Mask 3`:

* **Sobolev regularity.** `∫ (1 + |ξ|)^(2s) |𝓕 φ(ξ)|² dξ < ∞`, that is `φ ∈ H^s`, for every
  `s < 3 - log₂ 3` (`Daubechies.sobolev_scalingFun_order_three`). In terms of moduli of
  smoothness, `ω_r(φ, t)_p ≤ K t^s` for `p ≤ 2`, `0 < t ≤ 1` and `0 ≤ s < 3 - log₂ 3`, `s ≤ r`
  (`Daubechies.modulus_scalingFun_le_two_order_three`), and hence
  `‖(2^(ks) ω_r(φ, 2^(-k))_p)_k‖_{ℓ_q} < ∞` for every `q ≥ 1` and `0 ≤ s < min(r, 3 - log₂ 3)`
  (`Daubechies.lqNorm_modulus_scalingFun_lt_top_order_three`), which for `p = q = 2` is the
  Besov description `H^s = B^s_{2,2}`.
* **Hölder regularity.** `|φ(x) - φ(y)| ≤ K |x - y|^a` for every `0 ≤ a < 5/2 - log₂ 3 ≈ 0.915`
  (`Daubechies.holder_scalingFun_order_three`), in particular for `a = 9/10`
  (`Daubechies.holder_scalingFun_order_three_nine_tenths`), since `log₂ 3 < 8/5`.
* **Besov spaces by coefficients.** For `1 ≤ q ≤ ∞` and every `f ∈ L_p(ℝ)`,
  `‖f‖_p + ‖(2^(ks) ω_3(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff the coefficient quasi-norm
  `‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q}`
  (`Daubechies.coeffNorm`) is finite, for `1 ≤ p ≤ 2` and `0 < s < 3 - log₂ 3`
  (`Daubechies.besov_iff_coeff_order_three_le_two`) and for `2 ≤ p < ∞` and
  `0 < s < (2/p)(3 - log₂ 3) + (1 - 2/p)(5/2 - log₂ 3) = 5/2 - log₂ 3 + 1/p`
  (`Daubechies.besov_iff_coeff_order_three_two_le`), hence for every `1 ≤ p < ∞` and
  `0 < s < 5/2 - log₂ 3` (`Daubechies.besov_iff_coeff_order_three`); likewise with the
  Littlewood–Paley quasi-norm in place of the moduli of smoothness
  (`Daubechies.littlewoodPaleyNorm_lt_top_iff_coeff_order_three_le_two`,
  `Daubechies.littlewoodPaleyNorm_lt_top_iff_coeff_order_three_two_le`).

The characterisations are the general theorems `Daubechies.besov_iff_coeff_of_le_two` and
`Daubechies.besov_iff_coeff_of_two_le` for the growth bound of order three. For `p > 2` they need
orders `s' < 3 - log₂ 3` and `a < 5/2 - log₂ 3` with `s < (2/p) s' + (1 - 2/p) a`; since the
bound on `s` is strict, both orders can be taken a common `ε > 0` below their bounds
(`Daubechies.exists_orders_of_lt_interp`, `Daubechies.exists_orders_order_three`). The modulus of
smoothness has order `3` throughout (`Rd.lpModulus p 3`); every order `r > s` describes the same
space (`Rd.modNorm_le_modNorm_of_lt`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal FourierTransform
open ENNReal (dyadicWeight)

namespace Daubechies

/-! ### The exponents of order three -/

/-- **An upper bound for `log₂ 3`**: `log₂ 3 < 8/5`, since `3^5 = 243 < 256 = 2^8` (Mathlib's
`Real.log_lt_log`, `Real.log_pow`). Hence the Sobolev exponent of order three satisfies
`3 - log₂ 3 > 7/5` and the Hölder exponent `5/2 - log₂ 3 > 9/10`; together with
`log₂ 3 > 3/2` (`Daubechies.three_halves_lt_logb_two_three`) both lie in intervals of length
`1/10`. -/
theorem logb_two_three_lt_eight_fifths : Real.logb 2 3 < 8 / 5 := by
  rw [← Real.log_div_log, div_lt_iff₀ (Real.log_pos one_lt_two)]
  have h : Real.log (3 ^ 5) < Real.log (2 ^ 8) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- **Interpolated orders below their bounds**: for real `σ, α > 0`, every weight `w` and every
`s < w σ + (1 - w) α` there are `s', a` with `0 ≤ s' < σ`, `0 ≤ a < α` and
`s < w s' + (1 - w) a`. Take `s' = σ - ε` and `a = α - ε` with
`0 < ε < min(σ, α, w σ + (1 - w) α - s)` (Mathlib's `exists_between`); then
`w s' + (1 - w) a = w σ + (1 - w) α - ε > s`. -/
theorem exists_orders_of_lt_interp {w σ α s : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    (hs : s < w * σ + (1 - w) * α) :
    ∃ s' a : ℝ, 0 ≤ s' ∧ s' < σ ∧ 0 ≤ a ∧ a < α ∧ s < w * s' + (1 - w) * a := by
  obtain ⟨ε, hε0, hε⟩ := exists_between (lt_min (lt_min hσ hα) (sub_pos.2 hs))
  simp only [lt_min_iff] at hε
  obtain ⟨⟨hεσ, hεα⟩, hεs⟩ := hε
  refine ⟨σ - ε, α - ε, by linarith, by linarith, by linarith, by linarith, ?_⟩
  linarith [show w * (σ - ε) + (1 - w) * (α - ε) = w * σ + (1 - w) * α - ε by ring]

/-! ### Sobolev regularity -/

/-- **The weighted `L²` bound on the symbol product of order three**: for every Daubechies mask
of order `N = 3` and every real `s < 3 - log₂ 3 ≈ 1.415`,
`∫ (1 + |ξ|)^(2s) |Φ(ξ)|² dξ < ∞` for the symbol product `Φ` (`Daubechies.symbolProduct`).
This is `Daubechies.integrable_rpow_mul_normSq` for the growth bound `T^n 1 ≤ 2 · 9^n`
(`Daubechies.transferGrowth_three`), whose exponent is `3 - log₄ 9 = 3 - log₂ 3`
(`Daubechies.three_sub_logb_four_nine`). -/
theorem integrable_rpow_mul_normSq_order_three (m : Mask 3) {s : ℝ}
    (hs : s < 3 - Real.logb 2 3) :
    Integrable (fun ξ => (1 + |ξ|) ^ (2 * s) * ‖symbolProduct m ξ‖ ^ 2) :=
  integrable_rpow_mul_normSq m transferGrowth_three
    (by rw [Nat.cast_ofNat, three_sub_logb_four_nine]; exact hs)

/-- **The scaling function of order three lies in `H^s` for every `s < 3 - log₂ 3`**: for every
Daubechies mask of order `N = 3` and every real `s < 3 - log₂ 3 ≈ 1.415`,
`∫ (1 + |ξ|)^(2s) |𝓕 φ(ξ)|² dξ < ∞`, which is the Fourier description of the Sobolev space
`H^s(ℝ)`. The Fourier transform of `φ` is the symbol product `Φ`
(`Daubechies.fourier_scalingFun`), so this is
`Daubechies.integrable_rpow_mul_normSq_order_three`. -/
theorem sobolev_scalingFun_order_three (m : Mask 3) {s : ℝ} (hs : s < 3 - Real.logb 2 3) :
    Integrable (fun ξ => (1 + |ξ|) ^ (2 * s) * ‖𝓕 (scalingFun m) ξ‖ ^ 2) := by
  rw [fourier_scalingFun m (by norm_num)]
  exact integrable_rpow_mul_normSq_order_three m hs

/-- **Power bounds give finite Besov seminorms**: let `F : ℝ → [0, ∞]` satisfy `F(t) ≤ K t^θ`
for all `0 < t ≤ 1`, with a finite constant `K`. Then for every `s < θ` and `1 ≤ q ≤ ∞`,
`‖(2^(ks) F(2^(-k)))_k‖_{ℓ_q} < ∞`. Indeed `2^(ks) F(2^(-k)) ≤ K 2^(-k(θ - s))`
(`ENNReal.ofReal_one_div_two_pow_rpow`, `ENNReal.dyadicWeight_add`), and the geometric sequence
`(2^(-k(θ - s)))_k` has `ℓ_q` norm at most `(1 - 2^(-(θ - s)))⁻¹ < ∞`
(`ENNReal.lqNorm_dyadicWeight_neg_le`). -/
theorem lqNorm_dyadicWeight_mul_lt_top_of_le_rpow {F : ℝ → ℝ≥0∞} {K : ℝ≥0∞} (hK : K ≠ ∞)
    {θ : ℝ} (hF : ∀ t ∈ Set.Ioc (0 : ℝ) 1, F t ≤ K * ENNReal.ofReal (t ^ θ)) {s : ℝ}
    (hsθ : s < θ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ENNReal.lqNorm q (fun k : ℕ => dyadicWeight s k * F (1 / 2 ^ k)) < ∞ := by
  have hle : ∀ k : ℕ, dyadicWeight s k * F (1 / 2 ^ k) ≤ K * dyadicWeight (-(θ - s)) k := by
    intro k
    have ht : (1 / 2 ^ k : ℝ) ∈ Set.Ioc 0 1 :=
      ⟨by positivity, by rw [div_le_one (by positivity)]; exact one_le_pow₀ one_le_two⟩
    calc dyadicWeight s k * F (1 / 2 ^ k)
        ≤ dyadicWeight s k * (K * dyadicWeight (-θ) k) := by
          rw [← ENNReal.ofReal_one_div_two_pow_rpow]
          exact mul_le_mul_right (hF _ ht) _
      _ = K * dyadicWeight (-(θ - s)) k := by
          rw [mul_left_comm, ← ENNReal.dyadicWeight_add]
          congr 2
          ring
  calc ENNReal.lqNorm q (fun k : ℕ => dyadicWeight s k * F (1 / 2 ^ k))
      ≤ ENNReal.lqNorm q (fun k : ℕ => K * dyadicWeight (-(θ - s)) k) := ENNReal.lqNorm_mono hle
    _ = K * ENNReal.lqNorm q (dyadicWeight (-(θ - s))) := ENNReal.lqNorm_const_mul _ _
    _ ≤ K * (1 - (2 : ℝ≥0∞) ^ (-(θ - s)))⁻¹ :=
        mul_le_mul_right (ENNReal.lqNorm_dyadicWeight_neg_le hq _) _
    _ < ∞ := ENNReal.mul_lt_top hK.lt_top
        (ENNReal.one_sub_two_rpow_neg_inv_ne_top (by linarith)).lt_top

/-- **A Bernstein bound gives finite Besov seminorms of `φ`**: if the scaling function `φ` of a
Daubechies mask has a Bernstein bound `ω_r(φ, t)_p ≤ K t^θ` for `0 < t ≤ 1`
(`Daubechies.BernsteinBound`), then `‖(2^(ks) ω_r(φ, 2^(-k))_p)_k‖_{ℓ_q} < ∞` for every `s < θ`
and `1 ≤ q ≤ ∞` (`Daubechies.lqNorm_dyadicWeight_mul_lt_top_of_le_rpow`). -/
theorem BernsteinBound.lqNorm_modulus_lt_top {N : ℕ} {m : Mask N} {p : ℝ≥0∞} {θ : ℝ} {r : ℕ}
    (hB : BernsteinBound m p θ r) {s : ℝ} (hsθ : s < θ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ENNReal.lqNorm q
      (fun k : ℕ => dyadicWeight s k * Rd.modulus volume r p (scalingFun m) (1 / 2 ^ k)) < ∞ :=
  let ⟨_, hK, hmod⟩ := hB
  lqNorm_dyadicWeight_mul_lt_top_of_le_rpow hK hmod hsθ hq

/-- **The Besov seminorms of the scaling function of order three, `p ≤ 2`**: for every
Daubechies mask of order `N = 3`, every `p ≤ 2`, every `1 ≤ q ≤ ∞`, every order `r ∈ ℕ` and every
real `s` with `0 ≤ s < r` and `s < 3 - log₂ 3`,
`‖(2^(ks) ω_r(φ, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. For `p = q = 2` and `s > 0` this is the regularity
`φ ∈ H^s` in the Besov form `H^s = B^s_{2,2}`. The order `θ = (s + min(r, 3 - log₂ 3))/2` lies in
`(s, min(r, 3 - log₂ 3))`, so `φ` has a Bernstein bound of order `θ`
(`Daubechies.bernsteinBound_order_three`) and
`Daubechies.BernsteinBound.lqNorm_modulus_lt_top` applies. -/
theorem lqNorm_modulus_scalingFun_lt_top_order_three (m : Mask 3) {p : ℝ≥0∞} (hp2 : p ≤ 2)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {r : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hsr : s < r)
    (hs : s < 3 - Real.logb 2 3) :
    ENNReal.lqNorm q
      (fun k : ℕ => dyadicWeight s k * Rd.modulus volume r p (scalingFun m) (1 / 2 ^ k)) < ∞ := by
  have h1 : min (r : ℝ) (3 - Real.logb 2 3) ≤ r := min_le_left _ _
  have h2 : min (r : ℝ) (3 - Real.logb 2 3) ≤ 3 - Real.logb 2 3 := min_le_right _ _
  have h3 : s < min (r : ℝ) (3 - Real.logb 2 3) := lt_min hsr hs
  exact (bernsteinBound_order_three m hp2 (s := (s + min (r : ℝ) (3 - Real.logb 2 3)) / 2)
    (by linarith) (by linarith) (by linarith)).lqNorm_modulus_lt_top (by linarith) hq

/-! ### Hölder regularity -/

/-- **The scaling function of order three is Hölder continuous of order `9/10`**: for every
Daubechies mask of order `N = 3` there is a constant `K` with
`|φ(x) - φ(y)| ≤ K |x - y|^(9/10)` for all `x, y ∈ ℝ`. The Hölder estimate of order three
(`Daubechies.holder_scalingFun_order_three`) holds for every `0 ≤ a < 5/2 - log₂ 3 ≈ 0.915`, and
`9/10 < 5/2 - log₂ 3` since `log₂ 3 < 8/5` (`Daubechies.logb_two_three_lt_eight_fifths`). -/
theorem holder_scalingFun_order_three_nine_tenths (m : Mask 3) :
    ∃ K : ℝ, ∀ x y : ℝ, ‖scalingFun m x - scalingFun m y‖ ≤ K * |x - y| ^ (9 / 10 : ℝ) :=
  holder_scalingFun_order_three m (by norm_num) (by linarith [logb_two_three_lt_eight_fifths])

/-! ### Besov spaces by Daubechies coefficients -/

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Besov spaces by Daubechies coefficients of order three, `p ≤ 2`**: for every Daubechies
mask of order `N = 3`, every `1 ≤ p ≤ 2`, every `1 ≤ q ≤ ∞` and every `0 < s < 3 - log₂ 3`, an
`f ∈ L_p(ℝ)` satisfies `‖f‖_p + ‖(2^(ks) ω_3(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
(`Daubechies.coeffNorm`). This is `Daubechies.besov_iff_coeff_of_le_two` for the growth bound
`T^n 1 ≤ 2 · 9^n` (`Daubechies.transferGrowth_three`), whose exponent is
`3 - log₄ 9 = 3 - log₂ 3` (`Daubechies.three_sub_logb_four_nine`); `p ≤ 2` forces `p < ∞`. -/
theorem besov_iff_coeff_order_three_le_two (m : Mask 3) (hp2 : p ≤ 2) {s : ℝ} (hs : 0 < s)
    (hsl : s < 3 - Real.logb 2 3) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 3 f k) < ∞ ↔
      coeffNorm m p s q f < ∞ :=
  besov_iff_coeff_of_le_two m (by norm_num) (ne_top_of_le_ne_top ENNReal.ofNat_ne_top hp2) hp2
    transferGrowth_three hs (by rw [Nat.cast_ofNat, three_sub_logb_four_nine]; exact hsl) hq f

/-- **Littlewood–Paley blocks and Daubechies coefficients of order three, `p ≤ 2`**: for every
Daubechies mask of order `N = 3`, every `1 ≤ p ≤ 2`, every `1 ≤ q ≤ ∞` and every
`0 < s < 3 - log₂ 3`, the Littlewood–Paley quasi-norm `‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}`
(`Rd.littlewoodPaleyNorm`) of an `f ∈ L_p(ℝ)` is finite iff its coefficient quasi-norm
`Daubechies.coeffNorm` is (`Daubechies.littlewoodPaleyNorm_lt_top_iff_coeff_of_le_two` for the
growth bound `Daubechies.transferGrowth_three`). -/
theorem littlewoodPaleyNorm_lt_top_iff_coeff_order_three_le_two (m : Mask 3) (hp : p ≠ ∞)
    (hp2 : p ≤ 2) {s : ℝ} (hs : 0 < s) (hsl : s < 3 - Real.logb 2 3) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    Rd.littlewoodPaleyNorm hp s q f < ∞ ↔ coeffNorm m p s q f < ∞ :=
  littlewoodPaleyNorm_lt_top_iff_coeff_of_le_two m (by norm_num) hp hp2 transferGrowth_three hs
    (by rw [Nat.cast_ofNat, three_sub_logb_four_nine]; exact hsl) hq f

/-- **The orders of order three for `p ≥ 2`**: for every weight `w` and every
`s < w (3 - log₂ 3) + (1 - w)(5/2 - log₂ 3)` there are `s', a` with
`0 ≤ s' < 3 - log₄ 9`, `0 ≤ a < 3 - log₄ 9 - 1/2` and `s < w s' + (1 - w) a`, in the form that
`Daubechies.besov_iff_coeff_of_two_le` takes for the growth bound
`Daubechies.transferGrowth_three` (`Daubechies.exists_orders_of_lt_interp`; both bounds are
positive since `log₂ 3 < 8/5`, `Daubechies.logb_two_three_lt_eight_fifths`). -/
theorem exists_orders_order_three {w s : ℝ}
    (hs : s < w * (3 - Real.logb 2 3) + (1 - w) * (5 / 2 - Real.logb 2 3)) :
    ∃ s' a : ℝ, 0 ≤ s' ∧ s' < ((3 : ℕ) : ℝ) - Real.logb 4 9 ∧ 0 ≤ a ∧
      a < ((3 : ℕ) : ℝ) - Real.logb 4 9 - 1 / 2 ∧ s < w * s' + (1 - w) * a := by
  have hl := logb_two_three_lt_eight_fifths
  obtain ⟨s', a, hs'0, hs', ha0, ha, hsθ⟩ :=
    exists_orders_of_lt_interp (by linarith) (by linarith) hs
  rw [Nat.cast_ofNat, three_sub_logb_four_nine]
  exact ⟨s', a, hs'0, hs', ha0, by linarith, hsθ⟩

/-- **Besov spaces by Daubechies coefficients of order three, `p ≥ 2`**: for every Daubechies
mask of order `N = 3`, every `2 ≤ p < ∞`, every `1 ≤ q ≤ ∞` and every `s` with
`0 < s < (2/p)(3 - log₂ 3) + (1 - 2/p)(5/2 - log₂ 3)`, an `f ∈ L_p(ℝ)` satisfies
`‖f‖_p + ‖(2^(ks) ω_3(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
(`Daubechies.coeffNorm`). The bound on `s` equals `5/2 - log₂ 3 + 1/p`: it is `3 - log₂ 3` for
`p = 2` and decreases to the Hölder exponent `5/2 - log₂ 3` as `p → ∞`. Orders
`s' < 3 - log₂ 3` and `a < 5/2 - log₂ 3` with `s < (2/p) s' + (1 - 2/p) a`
(`Daubechies.exists_orders_order_three`) make `Daubechies.besov_iff_coeff_of_two_le` applicable
with the growth bound `Daubechies.transferGrowth_three`. -/
theorem besov_iff_coeff_order_three_two_le (m : Mask 3) (hp : p ≠ ∞) (hp2 : 2 ≤ p) {s : ℝ}
    (hs : 0 < s)
    (hsθ : s < 2 / p.toReal * (3 - Real.logb 2 3) + (1 - 2 / p.toReal) * (5 / 2 - Real.logb 2 3))
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 3 f k) < ∞ ↔
      coeffNorm m p s q f < ∞ :=
  let ⟨_, _, hs'0, hs', ha0, ha, hsθ'⟩ := exists_orders_order_three hsθ
  besov_iff_coeff_of_two_le m (by norm_num) hp hp2 transferGrowth_three hs'0 hs' ha0 ha hs hsθ'
    hq f

/-- **Littlewood–Paley blocks and Daubechies coefficients of order three, `p ≥ 2`**: for every
Daubechies mask of order `N = 3`, every `2 ≤ p < ∞`, every `1 ≤ q ≤ ∞` and every `s` with
`0 < s < (2/p)(3 - log₂ 3) + (1 - 2/p)(5/2 - log₂ 3)`, the Littlewood–Paley quasi-norm
`‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}` (`Rd.littlewoodPaleyNorm`) of an `f ∈ L_p(ℝ)` is finite iff its
coefficient quasi-norm `Daubechies.coeffNorm` is
(`Daubechies.littlewoodPaleyNorm_lt_top_iff_coeff_of_two_le` with the orders of
`Daubechies.exists_orders_order_three`). -/
theorem littlewoodPaleyNorm_lt_top_iff_coeff_order_three_two_le (m : Mask 3) (hp : p ≠ ∞)
    (hp2 : 2 ≤ p) {s : ℝ} (hs : 0 < s)
    (hsθ : s < 2 / p.toReal * (3 - Real.logb 2 3) + (1 - 2 / p.toReal) * (5 / 2 - Real.logb 2 3))
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    Rd.littlewoodPaleyNorm hp s q f < ∞ ↔ coeffNorm m p s q f < ∞ :=
  let ⟨_, _, hs'0, hs', ha0, ha, hsθ'⟩ := exists_orders_order_three hsθ
  littlewoodPaleyNorm_lt_top_iff_coeff_of_two_le m (by norm_num) hp hp2 transferGrowth_three hs'0
    hs' ha0 ha hs hsθ' hq f

/-- **Besov spaces by Daubechies coefficients of order three for every `p`**: for every
Daubechies mask of order `N = 3`, every `1 ≤ p < ∞`, every `1 ≤ q ≤ ∞` and every
`0 < s < 5/2 - log₂ 3 ≈ 0.915`, an `f ∈ L_p(ℝ)` satisfies
`‖f‖_p + ‖(2^(ks) ω_3(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
(`Daubechies.coeffNorm`). For `p ≤ 2` this is `Daubechies.besov_iff_coeff_order_three_le_two`,
since `5/2 - log₂ 3 < 3 - log₂ 3`; for `p ≥ 2` it is
`Daubechies.besov_iff_coeff_order_three_two_le`, since the bound there is
`5/2 - log₂ 3 + 1/p ≥ 5/2 - log₂ 3`. -/
theorem besov_iff_coeff_order_three (m : Mask 3) (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    (hsa : s < 5 / 2 - Real.logb 2 3) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 3 f k) < ∞ ↔
      coeffNorm m p s q f < ∞ := by
  rcases le_total p 2 with hp2 | hp2
  · exact besov_iff_coeff_order_three_le_two m hp2 hs (by linarith) hq f
  · have hw := (two_div_toReal_mem_Icc hp hp2).1
    exact besov_iff_coeff_order_three_two_le m hp hp2 hs (by linarith) hq f

end Lp

/-! ### Existence -/

/-- **A regular Daubechies wavelet of order three exists**: there is a Daubechies mask of order
`N = 3` (`Daubechies.exists_mask`), and its scaling function `φ` lies in `H^s` for every
`s < 3 - log₂ 3 ≈ 1.415`, `∫ (1 + |ξ|)^(2s) |𝓕 φ(ξ)|² dξ < ∞`
(`Daubechies.sobolev_scalingFun_order_three`), and is Hölder continuous of every order
`0 ≤ a < 5/2 - log₂ 3 ≈ 0.915` (`Daubechies.holder_scalingFun_order_three`). The Besov
characterisations of this file therefore apply to at least one mask. -/
theorem exists_mask_order_three_regular :
    ∃ m : Mask 3, (∀ s : ℝ, s < 3 - Real.logb 2 3 →
        Integrable (fun ξ => (1 + |ξ|) ^ (2 * s) * ‖𝓕 (scalingFun m) ξ‖ ^ 2)) ∧
      ∀ a : ℝ, 0 ≤ a → a < 5 / 2 - Real.logb 2 3 →
        ∃ K : ℝ, ∀ x y : ℝ, ‖scalingFun m x - scalingFun m y‖ ≤ K * |x - y| ^ a :=
  let ⟨m⟩ := exists_mask (N := 3) (by norm_num)
  ⟨m, fun _ hs => sobolev_scalingFun_order_three m hs,
    fun _ ha0 ha => holder_scalingFun_order_three m ha0 ha⟩

end Daubechies

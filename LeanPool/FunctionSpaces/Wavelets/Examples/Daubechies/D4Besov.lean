/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Besov

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces by D4 coefficients

For the Daubechies mask D4 (`Daubechies.d4`) with scaling function `φ` (`Daubechies.scalingFun`)
and wavelet `ψ` (`Daubechies.wavelet`), this file gives the explicit smoothness ranges in which
the Besov spaces `B^s_{p,q}(ℝ)` are described by the D4 coefficients. Let
`α = 2 - log₂(1 + √3) ≈ 0.5500` be the Hölder exponent of D4, and let `1 ≤ q ≤ ∞` and
`f ∈ L_p(ℝ)`. The **Besov condition** is
`‖f‖_p + ‖(2^(ks) ω_2(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` with differences of order `2`
(`Rd.lpModulus p 2`), and the **coefficient condition** is the finiteness of
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q}`
(`Daubechies.coeffNorm`).

* **Hölder regularity.** `‖φ(x) - φ(y)‖ ≤ K |x - y|^a` for every `0 ≤ a ≤ 0.55`
  (`Daubechies.holder_d4_of_le_055`), which is `Daubechies.holder_d4` together with
  `0.55 < α`; moreover `α < 1` (`Daubechies.two_sub_logb_two_one_add_sqrt_three_lt_one`).
* **`1 ≤ p ≤ 2`.** For `0 < s < 1` the Besov condition and the coefficient condition are
  equivalent (`Daubechies.besov_iff_coeff_d4_le_two`). The transfer operator of order two maps
  `1` to `4`, so its growth bound `T^n 1 ≤ 4^n` (`Daubechies.transferGrowth_two`) has the
  Sobolev exponent `2 - log₄ 4 = 1`, and `Daubechies.besov_iff_coeff_of_le_two` applies.
* **`2 ≤ p < ∞`.** For `0 < s < 2/p + (1 - 2/p) α` the two conditions are equivalent
  (`Daubechies.besov_iff_coeff_d4_two_le`). Since the bound is strict, there is `s' < 1` with
  `s < (2/p) s' + (1 - 2/p) α` (`Daubechies.exists_lt_mul_add_one_sub_mul`), and
  `φ` has a Bernstein bound of this interpolated order (`Daubechies.bernsteinBound_d4`,
  collected in `Daubechies.exists_bernsteinBound_d4_of_two_le`).
* **Every `1 ≤ p < ∞`.** For `0 < s < α` both ranges apply, so the two conditions are
  equivalent for every `p` (`Daubechies.besov_iff_coeff_d4`).
* **Littlewood–Paley.** In both ranges the coefficient condition is also equivalent to the
  finiteness of the Littlewood–Paley quasi-norm `‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}`
  (`Daubechies.littlewoodPaleyNorm_lt_top_iff_coeff_d4_le_two`,
  `Daubechies.littlewoodPaleyNorm_lt_top_iff_coeff_d4_two_le`).

The order `2` of the differences matches the order of D4; every order `r > s` describes the same
space, since the Besov quasi-norms of two such orders are equivalent
(`Rd.modNorm_le_modNorm_of_lt`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Real
open ENNReal (dyadicWeight)

namespace Daubechies

/-! ### The Hölder exponent of D4 -/

/-- **The Hölder exponent of D4 is below `1`**: `2 - log₂(1 + √3) < 1`, since `1 + √3 > 2`
(`Daubechies.one_lt_sqrt_three`) and `log₂` is strictly increasing with `log₂ 2 = 1`. -/
theorem two_sub_logb_two_one_add_sqrt_three_lt_one : 2 - Real.logb 2 (1 + √3) < 1 := by
  have h : Real.logb 2 2 < Real.logb 2 (1 + √3) :=
    Real.logb_lt_logb one_lt_two two_pos (by linarith [one_lt_sqrt_three])
  rw [Real.logb_self_eq_one one_lt_two] at h
  linarith

/-- **The Hölder exponent of D4 is positive**: `0 < 2 - log₂(1 + √3)`, since it exceeds `0.55`
(`Daubechies.two_sub_logb_two_one_add_sqrt_three_gt`). -/
theorem two_sub_logb_two_one_add_sqrt_three_pos : 0 < 2 - Real.logb 2 (1 + √3) :=
  lt_trans (by norm_num) two_sub_logb_two_one_add_sqrt_three_gt

/-- **D4 is Hölder continuous with exponent `0.55`**: for every real `a` with `0 ≤ a ≤ 0.55`
there is `K` with `‖φ(x) - φ(y)‖ ≤ K |x - y|^a` for all `x, y ∈ ℝ`, where `φ` is the scaling
function of D4. This is `Daubechies.holder_d4`, which holds for every
`0 ≤ a ≤ 2 - log₂(1 + √3)`, together with `0.55 < 2 - log₂(1 + √3)`
(`Daubechies.two_sub_logb_two_one_add_sqrt_three_gt`). -/
theorem holder_d4_of_le_055 {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 0.55) :
    ∃ K, ∀ x y, ‖scalingFun d4 x - scalingFun d4 y‖ ≤ K * |x - y| ^ a :=
  holder_d4 ha0 (ha.trans two_sub_logb_two_one_add_sqrt_three_gt.le)

/-! ### Bernstein bounds for D4 -/

/-- **Interpolated orders below a strict bound**: for a weight `w ∈ [0, 1]`, real `s, a` and
`b > 0` with `s < w b + (1 - w) a`, there is `s'` with `0 ≤ s' < b` and
`s < w s' + (1 - w) a`. With `ε = w b + (1 - w) a - s > 0`, the choice `s' = max(0, b - ε/2)`
works: `0 ≤ b - s' ≤ ε/2`, so `w b - w s' ≤ ε/2 < ε`. -/
theorem exists_lt_mul_add_one_sub_mul {w s a b : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) (hb : 0 < b)
    (hs : s < w * b + (1 - w) * a) :
    ∃ s', 0 ≤ s' ∧ s' < b ∧ s < w * s' + (1 - w) * a := by
  refine ⟨max 0 (b - (w * b + (1 - w) * a - s) / 2), le_max_left _ _,
    max_lt hb (by linarith), ?_⟩
  have h1 : b - (w * b + (1 - w) * a - s) / 2 ≤ max 0 (b - (w * b + (1 - w) * a - s) / 2) :=
    le_max_right _ _
  have h2 : max 0 (b - (w * b + (1 - w) * a - s) / 2) ≤ b := max_le hb.le (by linarith)
  have h3 := mul_le_of_le_one_left (sub_nonneg.2 h2) hw.2
  linarith

/-- **Bernstein bounds for D4 above a given smoothness, `p ≥ 2`**: for `2 ≤ p < ∞` and every
real `s < 2/p + (1 - 2/p) α` with `α = 2 - log₂(1 + √3)`, the scaling function of D4 has a
Bernstein bound `ω_2(φ, t)_p ≤ K t^θ` for `0 < t ≤ 1` (`Daubechies.BernsteinBound` with
differences of order `2`) of some order `θ` with `s < θ ≤ 1`. The order is
`θ = (2/p) s' + (1 - 2/p) α` for an `s' ∈ [0, 1)` with `s < θ`
(`Daubechies.exists_lt_mul_add_one_sub_mul`, the weight `2/p ∈ [0, 1]`), the bound is
`Daubechies.bernsteinBound_d4`, and `θ ≤ 1` since `s', α ≤ 1`. -/
theorem exists_bernsteinBound_d4_of_two_le {p : ℝ≥0∞} (hp : p ≠ ∞) (hp2 : 2 ≤ p) {s : ℝ}
    (hs : s < 2 / p.toReal + (1 - 2 / p.toReal) * (2 - Real.logb 2 (1 + √3))) :
    ∃ θ : ℝ, s < θ ∧ θ ≤ 1 ∧ BernsteinBound d4 p θ 2 := by
  have hw := two_div_toReal_mem_Icc hp hp2
  obtain ⟨s', hs'0, hs'1, hsθ⟩ := exists_lt_mul_add_one_sub_mul hw one_pos (by rwa [mul_one])
  exact ⟨_, hsθ, mul_add_one_sub_mul_le hw hs'1.le two_sub_logb_two_one_add_sqrt_three_lt_one.le,
    bernsteinBound_d4 hp2 one_le_two hs'0 hs'1 (by push_cast; linarith)
      two_sub_logb_two_one_add_sqrt_three_pos.le le_rfl⟩

/-! ### Besov spaces by D4 coefficients -/

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Besov spaces by D4 coefficients, `p ≤ 2`**: let `1 ≤ p ≤ 2`, `1 ≤ q ≤ ∞` and `0 < s < 1`.
Then for every `f ∈ L_p(ℝ)`,
`‖f‖_p + ‖(2^(ks) ω_2(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
(`Daubechies.coeffNorm`), with the scaling function `φ` and the wavelet `ψ` of D4. This is
`Daubechies.besov_iff_coeff_of_le_two` with the growth bound `T^n 1 ≤ 4^n`
(`Daubechies.transferGrowth_two`), whose exponent is `2 - log₄ 4 = 1`; `p ≤ 2` forces `p < ∞`.
Differences of any order `r > s` give the same condition (`Rd.modNorm_le_modNorm_of_lt`). -/
theorem besov_iff_coeff_d4_le_two (hp2 : p ≤ 2) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 2 f k) < ∞ ↔
      coeffNorm d4 p s q f < ∞ :=
  besov_iff_coeff_of_le_two d4 le_rfl (ne_top_of_le_ne_top ENNReal.ofNat_ne_top hp2) hp2
    transferGrowth_two hs (by rw [Nat.cast_ofNat, two_sub_logb_four_four]; exact hs1) hq f

/-- **Littlewood–Paley blocks and D4 coefficients, `p ≤ 2`**: let `1 ≤ p ≤ 2`, `1 ≤ q ≤ ∞` and
`0 < s < 1`. Then for every `f ∈ L_p(ℝ)` the Littlewood–Paley quasi-norm
`‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}` (`Rd.littlewoodPaleyNorm`) is finite iff the D4 coefficient
quasi-norm `Daubechies.coeffNorm` is (`Daubechies.littlewoodPaleyNorm_lt_top_iff_coeff_of_le_two`
with `Daubechies.transferGrowth_two`). -/
theorem littlewoodPaleyNorm_lt_top_iff_coeff_d4_le_two (hp : p ≠ ∞) (hp2 : p ≤ 2) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    Rd.littlewoodPaleyNorm hp s q f < ∞ ↔ coeffNorm d4 p s q f < ∞ :=
  littlewoodPaleyNorm_lt_top_iff_coeff_of_le_two d4 le_rfl hp hp2 transferGrowth_two hs
    (by rw [Nat.cast_ofNat, two_sub_logb_four_four]; exact hs1) hq f

/-- **Besov spaces by D4 coefficients, `p ≥ 2`**: let `2 ≤ p < ∞`, `1 ≤ q ≤ ∞` and
`0 < s < 2/p + (1 - 2/p) α` with the Hölder exponent `α = 2 - log₂(1 + √3) ≈ 0.5500` of D4.
Then for every `f ∈ L_p(ℝ)`,
`‖f‖_p + ‖(2^(ks) ω_2(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
(`Daubechies.coeffNorm`). This is `Daubechies.besov_iff_coeff` with a Bernstein bound of an order
`θ > s` (`Daubechies.exists_bernsteinBound_d4_of_two_le`). The bound decreases from `1` at
`p = 2` to `α` as `p → ∞`. Differences of any order `r > s` give the same condition
(`Rd.modNorm_le_modNorm_of_lt`). -/
theorem besov_iff_coeff_d4_two_le (hp : p ≠ ∞) (hp2 : 2 ≤ p) {s : ℝ} (hs : 0 < s)
    (hsb : s < 2 / p.toReal + (1 - 2 / p.toReal) * (2 - Real.logb 2 (1 + √3))) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 2 f k) < ∞ ↔
      coeffNorm d4 p s q f < ∞ := by
  obtain ⟨θ, hsθ, -, hB⟩ := exists_bernsteinBound_d4_of_two_le hp hp2 hsb
  exact besov_iff_coeff d4 le_rfl hp hB hs hsθ hq f

/-- **Littlewood–Paley blocks and D4 coefficients, `p ≥ 2`**: let `2 ≤ p < ∞`, `1 ≤ q ≤ ∞` and
`0 < s < 2/p + (1 - 2/p) α` with `α = 2 - log₂(1 + √3)`. Then for every `f ∈ L_p(ℝ)` the
Littlewood–Paley quasi-norm `‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}` (`Rd.littlewoodPaleyNorm`) is finite
iff the D4 coefficient quasi-norm `Daubechies.coeffNorm` is
(`Daubechies.littlewoodPaleyNorm_lt_top_iff_coeff` with the Bernstein bound of
`Daubechies.exists_bernsteinBound_d4_of_two_le`, whose order `θ ≤ 1` gives `s < 2`). -/
theorem littlewoodPaleyNorm_lt_top_iff_coeff_d4_two_le (hp : p ≠ ∞) (hp2 : 2 ≤ p) {s : ℝ}
    (hs : 0 < s)
    (hsb : s < 2 / p.toReal + (1 - 2 / p.toReal) * (2 - Real.logb 2 (1 + √3))) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure ℝ)) :
    Rd.littlewoodPaleyNorm hp s q f < ∞ ↔ coeffNorm d4 p s q f < ∞ := by
  obtain ⟨θ, hsθ, hθ1, hB⟩ := exists_bernsteinBound_d4_of_two_le hp hp2 hsb
  exact littlewoodPaleyNorm_lt_top_iff_coeff d4 le_rfl hp hB hs hsθ (by push_cast; linarith) hq f

/-- **Besov spaces by D4 coefficients for every `p`**: let `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and
`0 < s < α = 2 - log₂(1 + √3) ≈ 0.5500`. Then for every `f ∈ L_p(ℝ)`,
`‖f‖_p + ‖(2^(ks) ω_2(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + 1/2 - 1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
(`Daubechies.coeffNorm`). For `p ≤ 2` this is `Daubechies.besov_iff_coeff_d4_le_two`, since
`α < 1`; for `p ≥ 2` it is `Daubechies.besov_iff_coeff_d4_two_le`, since
`α ≤ 2/p + (1 - 2/p) α`. -/
theorem besov_iff_coeff_d4 (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    (hsα : s < 2 - Real.logb 2 (1 + √3)) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 2 f k) < ∞ ↔
      coeffNorm d4 p s q f < ∞ := by
  have hα1 := two_sub_logb_two_one_add_sqrt_three_lt_one
  rcases le_total p 2 with hp2 | hp2
  · exact besov_iff_coeff_d4_le_two hp2 hs (hsα.trans hα1) hq f
  · have hw := two_div_toReal_mem_Icc hp hp2
    have h := mul_nonneg hw.1 (sub_nonneg.2 hα1.le)
    exact besov_iff_coeff_d4_two_le hp hp2 hs (by linarith) hq f

end Lp

end Daubechies

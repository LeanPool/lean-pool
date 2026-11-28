/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.HaarBesov
public import LeanPool.FunctionSpaces.Domains.Interval.PiecewiseInverse
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.EFunctionalModuli

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Dyadic step functions in `L_p[0, 1]`, `0 < p ≤ 1`

For `0 < p < 1` the space `L_p[0, 1]` is a quasi-Banach space: Mathlib's `Lp ℂ p vol` is an
abelian group with the quasi-norm `‖·‖ₑ`, and the `p`-th power of the quasi-norm is subadditive,
`‖f + g‖_p^p ≤ ‖f‖_p^p + ‖g‖_p^p` (`MeasureTheory.Lp.enorm_add_rpow_le_of_le_one`). Approximation
by dyadic step functions is described by the **step couple** `Haar.stepCouple p`, the couple of
the quasi-norm and of the increasing subgroups `V_j` of `ℱ_j`-measurable elements, the step
functions of level `j` (`InterpCouple.ofMonotoneSubgroups`): its E-functional at `t = 2^j` is the
error of best approximation from `V_j` (`Haar.eFunctional_stepCouple_two_pow`), and its spaces
`E_{s,q}` are the approximation spaces `A^s_q(L_p, steps)`. For `1 ≤ p` the step couple is the
complexity couple of the Haar scheme (`Haar.stepCouple_eq_complexityCouple`,
`Haar.memEMethod_stepCouple_iff_memApprox`).

The modulus of smoothness `ω_r(f, t, [0, 1])_p` satisfies, for `0 < p ≤ 1`,
`ω_r(f + g, t)_p^p ≤ ω_r(f, t)_p^p + ω_r(g, t)_p^p` and `ω_r(f, t)_p ≤ 2^(r/p) ‖f‖_p`
(`Interval.modulus_add_rpow_le`, `Interval.modulus_le_of_le_one`, and their forms on `L_p`,
`Interval.lpModulus_add_rpow_le`, `Interval.lpModulus_le_of_le_one`). Two inequalities connect
it with the steps:

* **Jackson's inequality by averaging**, `E(2^j, f)_p ≤ 2^(1/p) ω_1(f, 2^(-j), [0, 1])_p` for
  every `0 < p < ∞` (`Haar.eFunctional_stepCouple_le`). On each dyadic interval `I` some value
  `f(y)` approximates `f` at least as well as the mean over `y` of `∫_I |f - f(y)|^p`
  (`MeasureTheory.exists_setLIntegral_enorm_sub_rpow_le`, the first moment method), and the double
  integrals over the dyadic squares add up to at most `2 ω_1(f, 2^(-j))_p^p`
  (`Interval.two_pow_mul_sum_lintegral_le_modulus`). The proof averages pointwise and uses
  Tonelli's theorem, so it holds for every `0 < p < ∞` with the constant `2^(1/p)`.
* **The inverse inequality of order `1/p`**: for a step function `a` of level `j`,
  `ω_1(a, 2^(-k), [0, 1])_p ≤ 2^(1/p) 2^(-(k-j)/p) ‖a‖_p` (`Haar.lpModulus_le_of_mem_lpMeas`).
  A difference `Δ_h a` lives on strips of width `h` left of the jumps, where
  `|Δ_h a|^p ≤ |a_n|^p + |a_{n+1}|^p` (`Interval.enorm_higherDiff_one_rpow_le_stripBound`), and
  the strip integral of the piecewise polynomials, `Interval.eLpNorm_le_of_strip`, adds these up
  (`Interval.eLpNorm_higherDiff_one_le_of_step`).

With the coincidence theorem for `ρ`-normed couples (`InterpCouple.ModulusData`, here
`Haar.stepModulusData` with `ρ = p` and `θ = 1/p`) this gives, for `0 < p ≤ 1`, `q ≠ 0` and
`0 < s < 1/p` (`Haar.memEMethod_stepCouple_iff_modulus`),

`f ∈ A^s_q(L_p[0, 1], steps)  ↔  ‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`,

the Besov space `B^s_{p,q,1}[0, 1]` of the first modulus (P. Oswald, *Approximation by splines in
the `L_p` metric, `0 < p < 1`*, Math. Nachr. 94 (1980), Theorem 6, in Russian; see Oswald,
*Haar system as Schauder basis in Besov spaces: The limiting cases for `0 < p ≤ 1`*,
[arXiv:1808.08156](https://arxiv.org/abs/1808.08156), (7), for `p < 1` and `q < ∞`).
Oswald's later [arXiv:2002.12917](https://arxiv.org/abs/2002.12917), Lemma 1, includes `p = 1`
and discusses `q = ∞`. The Lean result is the univariate membership equivalence for complex
functions. For `s < 1` the first-modulus space is the Besov space of DeVore–Popov
(Trans. Amer. Math. Soc. 305 (1988), (2.4) with `r = 1`, Theorem 5.1). For
`1/p - 1 < s < 1` and `q < ∞` it is also the Fourier-analytic `B^s_{p,q}[0, 1]`
(Oswald 2018, (2)). For `s > 1`, and for `s = 1` with
`q < ∞`, it differs from the space of the second modulus: the line `x ↦ x` has `ω_2 = 0`
(`Haar.lpModulus_two_idLp`) but `E(2^j, x)_p ≥ 2^(-1/p) 2^(-j)/4`
(`Haar.le_eFunctional_stepCouple_idLp`), so it lies outside `A^s_q(L_p, steps)`
(`Haar.not_memEMethod_stepCouple_idLp`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open Rd (higherDiff measurable_higherDiff)
open scoped ENNReal
open ENNReal (dyadicWeight lqNorm)

/-! ### The quasi-norm of `L_p` and the first moment method -/

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The quasi-norm of `L_p(μ)` vanishes at `0`, for every `p`. -/
theorem Lp.eNorm_zero {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} :
    ‖(0 : Lp E p μ)‖ₑ = 0 := by
  rw [Lp.eNorm_def, eLpNorm_congr_ae (Lp.coeFn_zero E p μ), eLpNorm_zero]

/-- The quasi-norm of `L_p(μ)` is even, `‖-f‖_p = ‖f‖_p`, for every `p`. -/
theorem Lp.eNorm_neg {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} (f : Lp E p μ) :
    ‖-f‖ₑ = ‖f‖ₑ := by
  rw [Lp.eNorm_def, Lp.eNorm_def, eLpNorm_congr_ae (Lp.coeFn_neg f), eLpNorm_neg]

/-- **The `p`-th power of the quasi-norm of `L_p` is subadditive for `p ≤ 1`**:
`‖f + g‖_p^p ≤ ‖f‖_p^p + ‖g‖_p^p` for `f, g ∈ L_p(μ)`, from the same inequality for functions
(`MeasureTheory.eLpNorm_add_rpow_le_of_le_one`). At `p = 0` both sides are powers `x^0 = 1`. -/
theorem Lp.enorm_add_rpow_le_of_le_one {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (hp1 : p ≤ 1) (f g : Lp E p μ) :
    ‖f + g‖ₑ ^ p.toReal ≤ ‖f‖ₑ ^ p.toReal + ‖g‖ₑ ^ p.toReal := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [ENNReal.toReal_zero, ENNReal.rpow_zero]
    exact le_self_add
  rw [Lp.eNorm_def, Lp.eNorm_def, Lp.eNorm_def, eLpNorm_congr_ae (Lp.coeFn_add f g)]
  exact eLpNorm_add_rpow_le_of_le_one hp0 hp1 _ _

/-- **A value of `F` approximates `F` on `s` at least as well as the mean of all values** (the
first moment method, Mathlib's `exists_le_setLAverage`): for measurable `F`, a set `s` of finite
positive measure and every exponent `r`, some `y ∈ s` has
`∫_s |F(x) - F(y)|^r dx ≤ μ(s)⁻¹ ∫_s ∫_s |F(x) - F(z)|^r dx dz`. -/
theorem exists_setLIntegral_enorm_sub_rpow_le [SFinite μ] {F : α → ℂ} (hF : Measurable F)
    {s : Set α} (hμ0 : μ s ≠ 0) (hμ : μ s ≠ ∞) (r : ℝ) :
    ∃ y ∈ s, ∫⁻ x in s, ‖F x - F y‖ₑ ^ r ∂μ ≤
      (μ s)⁻¹ * ∫⁻ y in s, ∫⁻ x in s, ‖F x - F y‖ₑ ^ r ∂μ ∂μ := by
  have hG : Measurable fun y => ∫⁻ x in s, ‖F x - F y‖ₑ ^ r ∂μ :=
    Measurable.lintegral_prod_left' (f := fun z : α × α => ‖F z.1 - F z.2‖ₑ ^ r)
      (((hF.comp measurable_fst).sub (hF.comp measurable_snd)).eNorm.pow_const r)
  obtain ⟨y, hy, hle⟩ := exists_le_setLAverage hμ0 hμ hG.aemeasurable
  exact ⟨y, hy, hle.trans_eq (by rw [setLAverage_eq, ENNReal.div_eq_inv_mul])⟩

end MeasureTheory

/-! ### Averages over dyadic intervals -/

namespace Interval

variable {p : ℝ≥0∞}

/-- **Steps from point values**: for measurable `F : ℝ → ℂ`, every exponent `r` and every `j`
there are values `c_n` such that the step function `u = ∑_{n<2^j} 1_{I_{j,n}} c_n` satisfies
`∫_0^1 |F - u|^r ≤ 2^j ∑_{n<2^j} ∫_{I_{j,n}} ∫_{I_{j,n}} |F(x) - F(y)|^r dx dy`: on each dyadic
interval `c_n = F(y_n)` for a point `y_n` of
`MeasureTheory.exists_setLIntegral_enorm_sub_rpow_le`, and `|I_{j,n}| = 2^(-j)`. -/
theorem exists_ppFun_lintegral_le {F : ℝ → ℂ} (hF : Measurable F) (r : ℝ) (j : ℕ) :
    ∃ c : ℕ → ℂ, ∫⁻ x in Icc 0 1, ‖F x - ppFun j (fun n => C (c n)) x‖ₑ ^ r ≤
      2 ^ j * ∑ n ∈ Finset.range (2 ^ j),
        ∫⁻ y in dyadicIco j n, ∫⁻ x in dyadicIco j n, ‖F x - F y‖ₑ ^ r := by
  have h0 : ∀ n, volume (dyadicIco j n) ≠ 0 := fun n => by
    rw [volume_dyadicIco_eq_inv]
    exact ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have ht : ∀ n, volume (dyadicIco j n) ≠ ∞ := fun n => by
    rw [volume_dyadicIco_eq_inv]
    exact ENNReal.inv_ne_top.2 (pow_ne_zero j two_ne_zero)
  choose y hy hle using fun n => exists_setLIntegral_enorm_sub_rpow_le hF (h0 n) (ht n) r
  refine ⟨fun n => F (y n), ?_⟩
  rw [lintegral_unit_eq_sum_dyadicIco _ j, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hcongr : ∫⁻ x in dyadicIco j n, ‖F x - ppFun j (fun n => C (F (y n))) x‖ₑ ^ r =
      ∫⁻ x in dyadicIco j n, ‖F x - F (y n)‖ₑ ^ r :=
    setLIntegral_congr_fun (measurableSet_dyadicIco j n) fun x hx => by
      rw [ppFun_eq_of_mem _ (Finset.mem_range.1 hn) hx]
      simp [polyFun]
  rw [hcongr]
  exact (hle n).trans_eq (by rw [volume_dyadicIco_eq_inv, inv_inv])

/-- **An integral over a dyadic interval as an integral over steps**: for `y ∈ I_{j,n}`,
`n < 2^j`, and every `g ≥ 0`, `∫_{I_{j,n}} g ≤ ∫_{|h| < 2^(-j)} 1_{[0, 1]}(y + h) g(y + h) dh`,
by the substitution `x = y + h` (Mathlib's `lintegral_add_left_eq_self`), since `y + h ∈ I_{j,n}`
forces `|h| < 2^(-j)` and `y + h ∈ [0, 1]`. -/
theorem setLIntegral_dyadicIco_le {j n : ℕ} (hn : n < 2 ^ j) (g : ℝ → ℝ≥0∞) {y : ℝ}
    (hy : y ∈ dyadicIco j n) :
    ∫⁻ x in dyadicIco j n, g x ≤
      ∫⁻ h in Ioo (-(1 / 2 ^ j)) (1 / 2 ^ j), (Icc (0 : ℝ) 1).indicator g (y + h) := by
  rw [← lintegral_indicator (measurableSet_dyadicIco j n),
    ← lintegral_add_left_eq_self ((dyadicIco j n).indicator g) y,
    ← lintegral_indicator measurableSet_Ioo]
  refine lintegral_mono fun h => ?_
  by_cases hm : y + h ∈ dyadicIco j n
  · have hIcc : y + h ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self (dyadicIco_subset hn hm)
    have hsplit : ((n : ℝ) + 1) / 2 ^ j = n / 2 ^ j + 1 / 2 ^ j := add_div _ _ _
    have hh : h ∈ Ioo (-(1 / 2 ^ j : ℝ)) (1 / 2 ^ j) := by
      rw [dyadicIco, mem_Ico] at hy hm
      constructor <;> linarith [hy.1, hy.2, hm.1, hm.2]
    simp only [Set.indicator_of_mem hm, Set.indicator_of_mem hh, Set.indicator_of_mem hIcc]
    exact le_rfl
  · simp only [Set.indicator_of_notMem hm]
    exact zero_le

/-- **The integral over `y` of a difference with step `h`**: for `0 < p < ∞`, measurable `F` and
every `h`, `∫_0^1 1_{[0, 1]}(y + h) |F(y + h) - F(y)|^p dy = ‖Δ_h(F, ·, [0, 1])‖_p^p`, with the
restricted difference of `Rd.modulusOn`. -/
theorem lintegral_indicator_add_eq_eLpNorm (hp0 : p ≠ 0) (hp : p ≠ ∞) {F : ℝ → ℂ}
    (hF : Measurable F) (h : ℝ) :
    ∫⁻ y in Icc 0 1, (Icc (0 : ℝ) 1).indicator (fun x => ‖F x - F y‖ₑ ^ p.toReal) (y + h) =
      eLpNorm ((Rd.stepSet (Icc (0 : ℝ) 1) 1 h).indicator ((fwdDiff h)^[1] F)) p volume ^
        p.toReal := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hmem : ∀ y : ℝ, y ∈ Rd.stepSet (Icc (0 : ℝ) 1) 1 h ↔
      y ∈ Icc (0 : ℝ) 1 ∧ y + h ∈ Icc (0 : ℝ) 1 := fun y => by
    simp only [Rd.stepSet, Set.mem_ofPred_eq]
    constructor
    · intro H
      exact ⟨by simpa using H 0 (Nat.zero_le 1), by simpa using H 1 le_rfl⟩
    · rintro ⟨h0, h1⟩ l hl
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hl with rfl | rfl
      · simpa using h0
      · simpa using h1
  rw [eLpNorm_rpow_eq (g := (Rd.stepSet (Icc (0 : ℝ) 1) 1 h).indicator ((fwdDiff h)^[1] F))
    ((measurable_higherDiff hF 1 h).indicator
      (Rd.measurableSet_stepSet measurableSet_Icc 1 h)).aestronglyMeasurable hp0 hp,
    ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ Icc (0 : ℝ) 1 ∧ y + h ∈ Icc (0 : ℝ) 1
  · simp only [Set.indicator_of_mem hy.1, Set.indicator_of_mem hy.2,
      Set.indicator_of_mem ((hmem y).2 hy), Function.iterate_one, fwdDiff]
  · rw [Set.indicator_of_notMem (fun h' => hy ((hmem y).1 h')), eNorm_zero,
      ENNReal.zero_rpow_of_pos hq]
    by_cases hy1 : y ∈ Icc (0 : ℝ) 1
    · simp only [Set.indicator_of_mem hy1, Set.indicator_of_notMem (fun h2 => hy ⟨hy1, h2⟩)]
    · simp only [Set.indicator_of_notMem hy1]

/-- **The double integral over the dyadic squares by the modulus**: for `0 < p < ∞` and
measurable `F`,
`2^j ∑_{n<2^j} ∫_{I_{j,n}} ∫_{I_{j,n}} |F(x) - F(y)|^p dx dy ≤ 2 ω_1(F, 2^(-j), [0, 1])_p^p`.
After the substitution `x = y + h` (`Interval.setLIntegral_dyadicIco_le`) and the exchange of the
integrals (Mathlib's `lintegral_lintegral_swap`), the integral over `y` is
`‖Δ_h(F, ·, [0, 1])‖_p^p ≤ ω_1(F, 2^(-j))_p^p` for each `|h| < 2^(-j)`
(`Interval.lintegral_indicator_add_eq_eLpNorm`), and these steps fill an interval of length
`2 · 2^(-j)`. -/
theorem two_pow_mul_sum_lintegral_le_modulus (hp0 : p ≠ 0) (hp : p ≠ ∞) {F : ℝ → ℂ}
    (hF : Measurable F) (j : ℕ) :
    2 ^ j * ∑ n ∈ Finset.range (2 ^ j),
      ∫⁻ y in dyadicIco j n, ∫⁻ x in dyadicIco j n, ‖F x - F y‖ₑ ^ p.toReal ≤
        2 * modulus 1 p 0 1 F (1 / 2 ^ j) ^ p.toReal := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set t : ℝ := 1 / 2 ^ j with ht
  set ω := modulus 1 p 0 1 F t
  set Φ : ℝ → ℝ → ℝ≥0∞ := fun y h =>
    (Icc (0 : ℝ) 1).indicator (fun x => ‖F x - F y‖ₑ ^ p.toReal) (y + h) with hΦdef
  have hΦ : Measurable (Function.uncurry Φ) := by
    have hfun : Function.uncurry Φ = fun z : ℝ × ℝ => if z.1 + z.2 ∈ Icc (0 : ℝ) 1 then
        ‖F (z.1 + z.2) - F z.1‖ₑ ^ p.toReal else 0 := by
      funext z
      simp only [Function.uncurry, hΦdef, Set.indicator_apply]
    rw [hfun]
    exact Measurable.ite ((measurable_fst.add measurable_snd) measurableSet_Icc)
      (((hF.comp (measurable_fst.add measurable_snd)).sub (hF.comp measurable_fst)).eNorm.pow_const
        _) measurable_const
  have h1 : ∑ n ∈ Finset.range (2 ^ j),
      ∫⁻ y in dyadicIco j n, ∫⁻ x in dyadicIco j n, ‖F x - F y‖ₑ ^ p.toReal ≤
        ∫⁻ y in Icc 0 1, ∫⁻ h in Ioo (-t) t, Φ y h :=
    (Finset.sum_le_sum fun n hn => setLIntegral_mono' (measurableSet_dyadicIco j n) fun y hy =>
      setLIntegral_dyadicIco_le (Finset.mem_range.1 hn) _ hy).trans
        (sum_lintegral_dyadicIco_le _ j)
  have h2 : ∫⁻ y in Icc 0 1, ∫⁻ h in Ioo (-t) t, Φ y h ≤
      ω ^ p.toReal * ENNReal.ofReal (t - -t) := by
    rw [lintegral_lintegral_swap hΦ.aemeasurable, ← Real.volume_Ioo, ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_Ioo fun h hh => ?_
    rw [hΦdef, lintegral_indicator_add_eq_eLpNorm hp0 hp hF h]
    exact ENNReal.rpow_le_rpow (Rd.eLpNorm_indicator_higherDiff_le_modulusOn
      (by rw [Real.norm_eq_abs]; exact abs_le.2 ⟨hh.1.le, hh.2.le⟩)) hq.le
  have h3 : (2 : ℝ≥0∞) ^ j * ENNReal.ofReal (t - -t) = 2 := by
    rw [show t - -t = 2 * t by ring, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ht,
      one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat, mul_left_comm,
      ENNReal.mul_inv_cancel (pow_ne_zero j two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
      mul_one]
  calc 2 ^ j * ∑ n ∈ Finset.range (2 ^ j),
        ∫⁻ y in dyadicIco j n, ∫⁻ x in dyadicIco j n, ‖F x - F y‖ₑ ^ p.toReal
      ≤ 2 ^ j * (ω ^ p.toReal * ENNReal.ofReal (t - -t)) := by gcongr; exact h1.trans h2
    _ = 2 * ω ^ p.toReal := by rw [mul_comm (ω ^ p.toReal), ← mul_assoc, h3]

/-! ### Differences of step functions -/

/-- **Differences of a step function**: let `u` take the value `v_n` on every dyadic interval
`I_{j,n}`, `n ∈ ℕ`, and let `0 < p ≤ 1`, `0 ≤ h ≤ 2^(-j)` and `x ≥ 0`. Then `|Δ_h u(x)|^p`
vanishes unless `x` lies in the strip of width `h` left of the right end of its interval
`I_{j,n}`, and there it is at most `|v_n|^p + |v_{n+1}|^p`, since `x + h ∈ I_{j,n+1}`: this is the
strip function `Interval.stripBound` with `r = 1`. -/
theorem enorm_higherDiff_one_rpow_le_stripBound (hp0 : p ≠ 0) (hp1 : p ≤ 1) {j : ℕ}
    {u : ℝ → ℂ} {v : ℕ → ℂ} (hu : ∀ n : ℕ, ∀ x ∈ dyadicIco j n, u x = v n) {h x : ℝ}
    (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ j) (hx : 0 ≤ x) :
    ‖higherDiff 1 h u x‖ₑ ^ p.toReal ≤
      stripBound j 1 h 1 (fun n => ‖v n‖ₑ ^ p.toReal + ‖v (n + 1)‖ₑ ^ p.toReal) x := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 (ne_top_of_le_ne_top ENNReal.one_ne_top hp1)
  have hq1 : p.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp1)
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hjh : 2 ^ j * h ≤ 1 := by
    rw [le_div_iff₀ hpos] at hh
    linarith
  have hd : higherDiff 1 h u x = u (x + h) - u x := higherDiff_succ 0 h u x
  have hxn : x ∈ dyadicIco j ⌊2 ^ j * x⌋₊ :=
    mem_dyadicIco.2 ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  rw [hd, stripBound, hu _ x hxn]
  have hxn' := mem_dyadicIco.1 hxn
  have hexp : 2 ^ j * (x + h) = 2 ^ j * x + 2 ^ j * h := mul_add _ _ _
  have hh2 : 0 ≤ 2 ^ j * h := mul_nonneg hpos.le hh0
  split_ifs with hbad
  · rw [Nat.cast_one, one_mul, div_le_iff₀ hpos] at hbad
    have hxh : x + h ∈ dyadicIco j (⌊2 ^ j * x⌋₊ + 1) := by
      rw [mem_dyadicIco]
      push_cast
      constructor <;> linarith
    rw [hu _ _ hxh, one_mul]
    calc ‖v (⌊2 ^ j * x⌋₊ + 1) - v ⌊2 ^ j * x⌋₊‖ₑ ^ p.toReal
        ≤ (‖v (⌊2 ^ j * x⌋₊ + 1)‖ₑ + ‖v ⌊2 ^ j * x⌋₊‖ₑ) ^ p.toReal :=
          ENNReal.rpow_le_rpow eNorm_sub_le hq.le
      _ ≤ ‖v (⌊2 ^ j * x⌋₊ + 1)‖ₑ ^ p.toReal + ‖v ⌊2 ^ j * x⌋₊‖ₑ ^ p.toReal :=
          ENNReal.rpow_add_le_add_rpow _ _ hq.le hq1
      _ = _ := add_comm _ _
  · rw [Nat.cast_one, one_mul, not_le, lt_div_iff₀ hpos] at hbad
    have hxh : x + h ∈ dyadicIco j ⌊2 ^ j * x⌋₊ := by
      rw [mem_dyadicIco]
      constructor <;> linarith
    rw [hu _ _ hxh, sub_self, eNorm_zero, ENNReal.zero_rpow_of_pos hq]

/-- **The `L_p` quasi-norm of a step function**: if `u = v_n` on `I_{j,n}` for `n < 2^j`, then
`∫_0^1 |u|^r = 2^(-j) ∑_{n<2^j} |v_n|^r` for every exponent `r`. -/
theorem lintegral_rpow_eq_of_step {j : ℕ} {u : ℝ → ℂ} {v : ℕ → ℂ}
    (hu : ∀ n < 2 ^ j, ∀ x ∈ dyadicIco j n, u x = v n) (r : ℝ) :
    ∫⁻ x in Icc 0 1, ‖u x‖ₑ ^ r = ((2 : ℝ≥0∞) ^ j)⁻¹ * ∑ n ∈ Finset.range (2 ^ j), ‖v n‖ₑ ^ r := by
  rw [lintegral_unit_eq_sum_dyadicIco _ j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [setLIntegral_congr_fun (measurableSet_dyadicIco j n) fun x hx => by
    rw [hu n (Finset.mem_range.1 hn) x hx], setLIntegral_const, volume_dyadicIco_eq_inv, mul_comm]

/-- **The inverse estimate for a step function of level `j`**: let `0 < p ≤ 1`, let `u` take the
value `v_n` on `I_{j,n}` for every `n ∈ ℕ`, with `v_{2^j} = 0`, and let `0 ≤ h ≤ 2^(-j)`. Then
`‖Δ_h u‖_{L_p[0, 1]} ≤ (2 · 2^j h)^(1/p) ‖u‖_{L_p[0, 1]}`. The strip function of
`Interval.enorm_higherDiff_one_rpow_le_stripBound` has the masses `M_n = |v_n|^p + |v_{n+1}|^p`,
whose sum over `n < 2^j` is at most `2 ∑_{n<2^j} |v_n|^p`, and the strip integral
`Interval.eLpNorm_le_of_strip` with `r = 1` gives the bound. -/
theorem eLpNorm_higherDiff_one_le_of_step (hp0 : p ≠ 0) (hp1 : p ≤ 1) {j : ℕ} {u : ℝ → ℂ}
    (hum : Measurable u) {v : ℕ → ℂ} (hu : ∀ n : ℕ, ∀ x ∈ dyadicIco j n, u x = v n)
    (hv : v (2 ^ j) = 0) {h : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ j) :
    eLpNorm (higherDiff 1 h u) p unitVol ≤
      (2 * ENNReal.ofReal (2 ^ j * h)) ^ (1 / p.toReal) * eLpNorm u p unitVol := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set a : ℕ → ℝ≥0∞ := fun n => ‖v n‖ₑ ^ p.toReal with ha_def
  set T := ∑ n ∈ Finset.range (2 ^ j), a n with hT
  have ha : a (2 ^ j) = 0 := by simp only [ha_def, hv, eNorm_zero, ENNReal.zero_rpow_of_pos hq]
  have hB : ∑ n ∈ Finset.range (2 ^ j), (a n + a (n + 1)) ≤
      (((1 : ℕ) : ℝ≥0∞) + 1) * (T ^ (1 / p.toReal)) ^ p.toReal := by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one, Nat.cast_one,
      one_add_one_eq_two, two_mul, Finset.sum_add_distrib]
    refine add_le_add le_rfl ?_
    calc ∑ n ∈ Finset.range (2 ^ j), a (n + 1)
        ≤ ∑ n ∈ Finset.range (2 ^ j), a (n + 1) + a 0 := le_self_add
      _ = T + a (2 ^ j) := by rw [hT, ← Finset.sum_range_succ', Finset.sum_range_succ]
      _ = T := by rw [ha, add_zero]
  refine (eLpNorm_le_of_strip hp0 hp subset_rfl (measurable_higherDiff hum 1 h).aestronglyMeasurable
    (r := 1) (h := h) (G := 1) (M := fun n => a n + a (n + 1)) ?_ hB).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [ENNReal.one_rpow]
    exact enorm_higherDiff_one_rpow_le_stripBound hp0 hp1 hu hh0 hh hx.1
  have hpinv : (0 : ℝ) ≤ 1 / p.toReal := by positivity
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hum.aestronglyMeasurable,
    lintegral_rpow_eq_of_step (fun n _ => hu n)]
  simp only [Nat.cast_one, one_mul]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hpinv, ← ENNReal.mul_rpow_of_nonneg _ _ hpinv]
  congr 1
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  calc ENNReal.ofReal h * (1 + 1) * T = 2 * ENNReal.ofReal h * T * (2 ^ j * (2 ^ j)⁻¹) := by
        rw [ENNReal.mul_inv_cancel (pow_ne_zero j two_ne_zero)
          (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), mul_one]
        ring
    _ = 2 * (2 ^ j * ENNReal.ofReal h) * ((2 ^ j)⁻¹ * T) := by ring

/-! ### The line on a dyadic interval -/

/-- **The line is far from constants on every dyadic interval**: for every `c ∈ ℂ` and every
exponent `r ≥ 0`, `∫_{I_{j,n}} |x - c|^r dx ≥ (2^(-j)/4)^r · 2^(-j)/2`, since at most half of
`I_{j,n}` lies within `2^(-j)/4` of `Re c`. -/
theorem le_lintegral_dyadicIco_enorm_sub_rpow (j n : ℕ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (1 / 2 ^ j / 4) ^ r * ENNReal.ofReal (1 / 2 ^ j / 2) ≤
      ∫⁻ x in dyadicIco j n, ‖(x : ℂ) - c‖ₑ ^ r := by
  set δ : ℝ := 1 / 2 ^ j with hδ
  have hδ0 : 0 < δ := by positivity
  set B := Ioo (c.re - δ / 4) (c.re + δ / 4)
  have hvol : ENNReal.ofReal (δ / 2) ≤ volume (dyadicIco j n \ B) := by
    calc ENNReal.ofReal (δ / 2) = volume (dyadicIco j n) - volume B := by
          rw [volume_dyadicIco, Real.volume_Ioo, ← ENNReal.ofReal_sub _ (by linarith)]
          congr 1
          ring
      _ ≤ volume (dyadicIco j n \ B) := le_measure_sdiff
  calc ENNReal.ofReal (δ / 4) ^ r * ENNReal.ofReal (δ / 2)
      ≤ ENNReal.ofReal (δ / 4) ^ r * volume (dyadicIco j n \ B) := by gcongr
    _ = ∫⁻ _ in dyadicIco j n \ B, ENNReal.ofReal (δ / 4) ^ r := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in dyadicIco j n \ B, ‖(x : ℂ) - c‖ₑ ^ r := by
        refine setLIntegral_mono' ((measurableSet_dyadicIco j n).diff measurableSet_Ioo)
          fun x hx => ENNReal.rpow_le_rpow ?_ hr
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        have hre : |x - c.re| ≤ ‖(x : ℂ) - c‖ := by simpa using Complex.abs_re_le_norm ((x : ℂ) - c)
        have hfar : δ / 4 ≤ |x - c.re| := by
          by_contra H
          obtain ⟨h1, h2⟩ := abs_lt.1 (not_le.1 H)
          exact hx.2 ⟨by linarith, by linarith⟩
        linarith
    _ ≤ ∫⁻ x in dyadicIco j n, ‖(x : ℂ) - c‖ₑ ^ r := lintegral_mono_set sdiff_subset

end Interval

/-! ### The couple of dyadic step functions -/

namespace Haar

open Interval

variable {p : ℝ≥0∞}

variable (p) in
/-- The **couple of dyadic step functions** in `L_p[0, 1]`, for every `p`: the quasi-norm
`N₀(f) = ‖f‖_p` and the complexity of the subgroups `V_j` of `ℱ_j`-measurable elements, the step
functions on the dyadic intervals of level `j`, with `V_j` at complexity `2^j`
(`InterpCouple.ofMonotoneSubgroups`). It uses the group structure and the quasi-norm `‖·‖ₑ` of
`Lp`, which exist for every `p`; for `1 ≤ p` it is the complexity couple of the Haar scheme
`Haar.scheme` (`Haar.stepCouple_eq_complexityCouple`). -/
noncomputable def stepCouple : InterpCouple (Lp ℂ p vol) :=
  InterpCouple.ofMonotoneSubgroups (fun f => ‖f‖ₑ)
    (fun j => lpMeasSubgroup ℂ (dyadicFiltration j) p vol)
    (dyadicFiltration.monotone_lpMeasSubgroup ℂ)

/-- **The E-functional of the step couple at `t = 2^j`** is the error of best approximation by
step functions of level `j`: `E(2^j, f) = inf {‖f - b‖_p : b ∈ L_p, b ℱ_j-measurable}`. -/
theorem eFunctional_stepCouple_two_pow (j : ℕ) (f : Lp ℂ p vol) :
    (stepCouple p).eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) f =
      ⨅ b ∈ lpMeasSubgroup ℂ (dyadicFiltration j) p vol, ‖f - b‖ₑ :=
  InterpCouple.eFunctional_ofMonotoneSubgroups_two_pow j f

/-- An element of complexity at most `2^j` in the step couple is `ℱ_j`-measurable, a step
function of level `j`. -/
theorem mem_lpMeas_of_stepCouple_norm1_le {j : ℕ} {a : Lp ℂ p vol}
    (ha : (stepCouple p).norm1 a ≤ ((2 ^ j : ℕ) : ℝ≥0∞)) :
    a ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol := by
  have h := InterpCouple.mem_of_complexity_norm1_le (N := fun f : Lp ℂ p vol => ‖f‖ₑ)
    (InterpCouple.monotone_dyadicLevels (dyadicFiltration.monotone_lpMeasSubgroup ℂ)) ha
  rw [InterpCouple.dyadicLevels_two_pow] at h
  exact h

/-- **For `1 ≤ p` the step couple is the complexity couple of the Haar scheme**: both are the
complexity couple of the norm of `L_p[0, 1]` and of the sets `{0}` at complexity `0` and the
`ℱ_⌊log₂ n⌋`-measurable elements at complexity `n ≥ 1`. -/
theorem stepCouple_eq_complexityCouple [Fact (1 ≤ p)] :
    stepCouple p = (scheme p).complexityCouple := by
  have hS : InterpCouple.dyadicLevels (fun j => lpMeasSubgroup ℂ (dyadicFiltration j) p vol) =
      (scheme p).sets := by
    funext n
    ext f
    rcases eq_or_ne n 0 with rfl | hn
    · rw [InterpCouple.dyadicLevels_zero, (scheme p).sets_zero]
    · simp only [InterpCouple.dyadicLevels, hn, ↓reduceIte, SetLike.mem_coe]
      rw [mem_lpMeasSubgroup_iff_aestronglyMeasurable]
      exact mem_lpMeas_iff_aestronglyMeasurable.symm.trans (dyadicFiltration.mem_scheme hn).symm
  change InterpCouple.complexity _ _ = InterpCouple.complexity _ _
  rw [hS]

/-- **For `1 ≤ p` the spaces of the step couple are the approximation spaces of the Haar
scheme**: for `s ≥ 0` and `q ≠ 0` with `s > 0` or `q = ∞`, `f ∈ E_{s,q}` iff
`f ∈ A^s_q(L_p, Haar)` (`ApproximationScheme.memEMethod_complexityCouple_iff`). -/
theorem memEMethod_stepCouple_iff_memApprox [Fact (1 ≤ p)] {s : ℝ} {q : ℝ≥0∞} (hs : 0 ≤ s)
    (hsq : 0 < s ∨ q = ∞) (hq0 : q ≠ 0) {f : Lp ℂ p vol} :
    (stepCouple p).MemEMethod s q f ↔ (scheme p).MemApprox s q f := by
  rw [stepCouple_eq_complexityCouple]
  exact ApproximationScheme.memEMethod_complexityCouple_iff hs hsq hq0

/-! ### Jackson's inequality by averaging -/

/-- **Jackson's inequality for dyadic steps in `L_p`, `0 < p < ∞`, by averaging**:
`E(2^j, f) ≤ 2^(1/p) ω_1(f, 2^(-j), [0, 1])_p` in the step couple. The step function takes on
each dyadic interval a value `f(y_n)` at least as good as the average
(`Interval.exists_ppFun_lintegral_le`), and the double integrals over the dyadic squares add up to
at most `2 ω_1(f, 2^(-j))_p^p` (`Interval.two_pow_mul_sum_lintegral_le_modulus`). The proof
averages pointwise and uses Tonelli's theorem, so it holds for every `0 < p < ∞`; at `p = 0` the
quasi-norm vanishes. -/
theorem eFunctional_stepCouple_le (hp : p ≠ ∞) (f : Lp ℂ p vol) (j : ℕ) :
    (stepCouple p).eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) f ≤
      2 ^ (1 / p.toReal) * lpModulus p 1 f j := by
  rcases eq_or_ne p 0 with rfl | hp0
  · refine (InterpCouple.eFunctional_le
      (InterpCouple.ofMonotoneSubgroups_norm1_zero.trans_le zero_le)).trans ?_
    simp
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hF : Measurable (f : ℝ → ℂ) := (Lp.stronglyMeasurable f).measurable
  obtain ⟨c, hc⟩ := exists_ppFun_lintegral_le hF p.toReal j
  have hQ : ∀ n, C (c n) ∈ degreeLT ℂ 1 := fun n =>
    mem_degreeLT.2 (degree_C_le.trans_lt (by norm_num))
  have hu : MemLp (ppFun j fun n => C (c n)) p vol := memLp_ppFun j _ p
  have hb : hu.toLp _ ∈ lpMeasSubgroup ℂ (dyadicFiltration j) p vol :=
    mem_lpMeasSubgroup_iff_aestronglyMeasurable.2 ⟨stepFun (ppFun j fun n => C (c n)) j,
      stronglyMeasurable_stepFun _ j, (MemLp.coeFn_toLp hu).trans (ppFun_ae_eq_stepFun hQ j)⟩
  rw [eFunctional_stepCouple_two_pow]
  refine (iInf₂_le _ hb).trans ?_
  rw [Lp.eNorm_def, eLpNorm_congr_ae ((Lp.coeFn_sub f _).trans
    (Filter.EventuallyEq.sub Filter.EventuallyEq.rfl (MemLp.coeFn_toLp hu)))]
  refine eLpNorm_le_of_lintegral_le (hF.sub (measurable_ppFun j _)).aestronglyMeasurable hp0 hp ?_
  calc ∫⁻ x, ‖((f : ℝ → ℂ) - ppFun j fun n => C (c n)) x‖ₑ ^ p.toReal ∂vol
      ≤ 2 ^ j * ∑ n ∈ Finset.range (2 ^ j),
          ∫⁻ y in dyadicIco j n, ∫⁻ x in dyadicIco j n, ‖f x - f y‖ₑ ^ p.toReal := hc
    _ ≤ 2 * lpModulus p 1 f j ^ p.toReal := two_pow_mul_sum_lintegral_le_modulus hp0 hp hF j
    _ = (2 ^ (1 / p.toReal) * lpModulus p 1 f j) ^ p.toReal := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne',
          ENNReal.rpow_one]

/-! ### The inverse inequality for jumps -/

/-- **The inverse inequality for dyadic steps in `L_p`, `0 < p ≤ 1`**, of order `1/p`: for an
`ℱ_j`-measurable `a ∈ L_p[0, 1]` and every `k`,
`ω_1(a, 2^(-k), [0, 1])_p ≤ 2^(1/p) 2^(-(k-j)/p) ‖a‖_p`, with `k - j` truncated at `0`. A
difference of first order of a step function lives on the strips at its jumps
(`Interval.enorm_higherDiff_one_rpow_le_stripBound`), so the order is `1/p`; DeVore–Popov's
general order `min(r, r - 1 + 1/p)` (their Theorem 4.8) is `1` for `r = 1`. -/
theorem lpModulus_le_of_mem_lpMeas (hp0 : p ≠ 0) (hp1 : p ≤ 1) {j k : ℕ} {a : Lp ℂ p vol}
    (ha : a ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) :
    lpModulus p 1 a k ≤ 2 ^ (1 / p.toReal) * dyadicWeight (-(1 / p.toReal)) (k - j) * ‖a‖ₑ := by
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (lpModulus_le_of_le_one hp1 1 a k).trans_eq (by rw [Nat.cast_one])
  obtain ⟨g, hg, hag⟩ := mem_lpMeas_iff_aestronglyMeasurable.1 ha
  have hae : (a : ℝ → ℂ) =ᵐ[vol] ppFun j fun m => C (g ((m : ℝ) / 2 ^ j)) :=
    hag.trans (ae_eq_ppFun_of_stronglyMeasurable hg)
  have hu : ∀ n : ℕ, ∀ x ∈ dyadicIco j n, ppFun j (fun m => C (g ((m : ℝ) / 2 ^ j))) x =
      if n < 2 ^ j then g ((n : ℝ) / 2 ^ j) else 0 := fun n x hx => by
    rw [ppFun_eq_polyFun _ hx]
    split_ifs <;> simp [polyFun]
  have hnorm : ‖a‖ₑ = eLpNorm (ppFun j fun m => C (g ((m : ℝ) / 2 ^ j))) p vol := by
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae hae
  rw [lpModulus, modulus_congr_ae hae, hnorm, modulus_eq_iSup_nonneg]
  refine iSup₂_le fun h hh => ?_
  have hhj : h ≤ 1 / 2 ^ j := hh.2.trans (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) hjk))
  have hsub : Icc (0 : ℝ) (1 - ((1 : ℕ) : ℝ) * h) ⊆ Icc 0 1 :=
    Icc_subset_Icc le_rfl (sub_le_self _ (mul_nonneg (Nat.cast_nonneg 1) hh.1))
  refine (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)).trans
    ((eLpNorm_higherDiff_one_le_of_step hp0 hp1 (measurable_ppFun j _) hu
      (by simp) hh.1 hhj).trans ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  gcongr
  exact ENNReal.ofReal_two_pow_mul_rpow_le hjk hh.2 (by positivity)

/-! ### The coincidence theorem -/

/-- **The first modulus is compatible with the step couple in `L_p`, `0 < p ≤ 1`**, with the
exponent `ρ = p` (the `p`-th power of the quasi-norm is subadditive) and inverse order
`θ = 1/p`: `ω_1(f, 2^(-k), [0, 1])_p ≤ 2^(1/p) ‖f‖_p`, Jackson's inequality
`E(2^k, f) ≤ 2^(1/p) ω_1(f, 2^(-k))_p` (`Haar.eFunctional_stepCouple_le`) and the inverse
inequality `ω_1(a, 2^(-k))_p ≤ 2^(1/p) 2^(-(k-j)/p) ‖a‖_p` for steps `a` of level `j`
(`Haar.lpModulus_le_of_mem_lpMeas`). -/
noncomputable def stepModulusData (hp0 : p ≠ 0) (hp1 : p ≤ 1) :
    (stepCouple p).ModulusData p.toReal (1 / p.toReal) where
  rho_pos := ENNReal.toReal_pos hp0 (ne_top_of_le_ne_top ENNReal.one_ne_top hp1)
  norm0_zero := Lp.eNorm_zero
  norm0_neg := Lp.eNorm_neg
  norm0_add_rpow_le := Lp.enorm_add_rpow_le_of_le_one hp1
  norm1_zero := InterpCouple.ofMonotoneSubgroups_norm1_zero
  norm1_neg := InterpCouple.ofMonotoneSubgroups_norm1_neg
  norm1_add_le := InterpCouple.ofMonotoneSubgroups_norm1_add_le
  modulus f k := lpModulus p 1 f k
  add_rpow_le f g k := lpModulus_add_rpow_le hp1 1 f g k
  C0 := 2 ^ (1 / p.toReal)
  C0_ne_top := ENNReal.two_rpow_ne_top _
  le_norm0 f k := (lpModulus_le_of_le_one hp1 1 f k).trans_eq (by rw [Nat.cast_one]; rfl)
  CJ := 2 ^ (1 / p.toReal)
  CJ_ne_top := ENNReal.two_rpow_ne_top _
  jackson f k := eFunctional_stepCouple_le (ne_top_of_le_ne_top ENNReal.one_ne_top hp1) f k
  CB := 2 ^ (1 / p.toReal)
  CB_ne_top := ENNReal.two_rpow_ne_top _
  inverse _ _ _ ha := lpModulus_le_of_mem_lpMeas hp0 hp1 (mem_lpMeas_of_stepCouple_norm1_le ha)

variable {s : ℝ} {q : ℝ≥0∞}

/-- **Dyadic steps in `L_p`, `0 < p ≤ 1`, in dyadic form**: for `0 ≤ s < 1/p` and every `q`,
`‖f‖_p + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q}` is finite iff the Besov quasi-norm of the first modulus
`‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q}` is finite. -/
theorem eNormDyadic_stepCouple_lt_top_iff_modulus (hp0 : p ≠ 0) (hp1 : p ≤ 1) (hs : 0 ≤ s)
    (hsp : s < 1 / p.toReal) (f : Lp ℂ p vol) :
    (stepCouple p).eNormDyadic s q f < ∞ ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 f k) < ∞ :=
  (stepModulusData hp0 hp1).eNormDyadic_lt_top_iff hs hsp f

/-- **Approximation by dyadic step functions in `L_p[0, 1]`, `0 < p ≤ 1`.** For `q ≠ 0` and
`0 < s < 1/p`, `f ∈ L_p[0, 1]` lies in the approximation space `E_{s,q}` of the step couple
(`A^s_q(L_p, steps)`) iff
`‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`, the space `B^s_{p,q,1}[0, 1]` of the
first modulus (Oswald, arXiv:2002.12917, Lemma 1 and the discussion of `q = ∞`).
For `s < 1` this is the Besov space of DeVore–Popov (1988), (2.4) with `r = 1`
(their Theorem 5.1 at `r = 1`). For `1/p - 1 < s < 1` and `q < ∞` it is also the
Fourier-analytic `B^s_{p,q}[0, 1]` (Oswald 2018, (2)). For `s > 1`,
and for `s = 1` with `q < ∞`, it misses the line `x ↦ x`, whose second modulus vanishes
(`Haar.not_memEMethod_stepCouple_idLp`). -/
theorem memEMethod_stepCouple_iff_modulus (hp0 : p ≠ 0) (hp1 : p ≤ 1) (hq0 : q ≠ 0)
    (hs : 0 < s) (hsp : s < 1 / p.toReal) (f : Lp ℂ p vol) :
    (stepCouple p).MemEMethod s q f ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 f k) < ∞ :=
  (stepModulusData hp0 hp1).memEMethod_iff_modNorm_lt_top
    (fun _ hb => InterpCouple.eq_zero_of_ofMonotoneSubgroups_norm1_lt_one hb) hq0 hs hsp f

/-! ### The line `x ↦ x` -/

variable (p) in
/-- The class of the line `x ↦ x` in `L_p[0, 1]`. -/
noncomputable def idLp : Lp ℂ p vol := (memLp_polyFun X p 0 1).toLp (polyFun X)

/-- **The line has vanishing second modulus in `L_p[0, 1]`**:
`ω_2(x ↦ x, 2^(-k), [0, 1])_p = 0` for every `p` and `k` (`Interval.modulus_two_id`). -/
theorem lpModulus_two_idLp (k : ℕ) : lpModulus p 2 (idLp p) k = 0 := by
  have hX : polyFun X = fun x : ℝ => (x : ℂ) := funext fun x => by simp [polyFun]
  rw [lpModulus, idLp, modulus_congr_ae (MemLp.coeFn_toLp _), hX]
  exact modulus_two_id p _

/-- **The line is far from the steps of level `j`**: for `0 < p < ∞`,
`E(2^j, x)_p ≥ 2^(-1/p) 2^(-j)/4` in the step couple, since every step function `b` of level `j`
has `‖x - b‖_p^p ≥ 2^j (2^(-j)/4)^p 2^(-j)/2` (`Interval.le_lintegral_dyadicIco_enorm_sub_rpow`).
-/
theorem le_eFunctional_stepCouple_idLp (hp0 : p ≠ 0) (hp : p ≠ ∞) (j : ℕ) :
    ENNReal.ofReal (1 / 2) ^ (1 / p.toReal) * ENNReal.ofReal (1 / 2 ^ j / 4) ≤
      (stepCouple p).eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) (idLp p) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eFunctional_stepCouple_two_pow]
  refine le_iInf₂ fun b hb => ?_
  obtain ⟨g, hg, hbg⟩ := mem_lpMeasSubgroup_iff_aestronglyMeasurable.1 hb
  set u := ppFun j fun m => C (g ((m : ℝ) / 2 ^ j))
  have hae : ⇑(idLp p - b) =ᵐ[vol] polyFun X - u := (Lp.coeFn_sub _ _).trans
    ((MemLp.coeFn_toLp _).sub (hbg.trans (ae_eq_ppFun_of_stronglyMeasurable hg)))
  have hcount : ((2 ^ j : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ j / 2) = ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    field_simp
  rw [Lp.eNorm_def, eLpNorm_congr_ae hae, ← ENNReal.rpow_le_rpow_iff hq,
    eLpNorm_rpow_eq ((measurable_polyFun X).sub (measurable_ppFun j _)).aestronglyMeasurable hp0 hp,
    ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne',
    ENNReal.rpow_one, ← hcount]
  calc ((2 ^ j : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ j / 2) *
        ENNReal.ofReal (1 / 2 ^ j / 4) ^ p.toReal
      = ∑ n ∈ Finset.range (2 ^ j),
          ENNReal.ofReal (1 / 2 ^ j / 4) ^ p.toReal * ENNReal.ofReal (1 / 2 ^ j / 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ ∑ n ∈ Finset.range (2 ^ j), ∫⁻ x in dyadicIco j n, ‖(polyFun X - u) x‖ₑ ^ p.toReal :=
        Finset.sum_le_sum fun n hn => by
          have hc : ∀ x ∈ dyadicIco j n, ‖(polyFun X - u) x‖ₑ ^ p.toReal =
              ‖(x : ℂ) - g ((n : ℝ) / 2 ^ j)‖ₑ ^ p.toReal := fun x hx => by
            simp only [u, Pi.sub_apply, ppFun_eq_of_mem _ (Finset.mem_range.1 hn) hx, polyFun,
              eval_X, eval_C]
          rw [setLIntegral_congr_fun (measurableSet_dyadicIco j n) hc]
          exact le_lintegral_dyadicIco_enorm_sub_rpow j n _ hq.le
    _ = ∫⁻ x in Icc 0 1, ‖(polyFun X - u) x‖ₑ ^ p.toReal :=
        (lintegral_unit_eq_sum_dyadicIco _ j).symm

/-- **The line is not approximated by steps at a rate `s > 1`, nor at the rate `1` in `ℓ_q`,
`q < ∞`**: for `0 < p < ∞`, `q ≠ 0` and `s ≥ 1` with `s > 1` or `q < ∞`, the line `x ↦ x` does
not lie in `E_{s,q}` of the step couple. By `Haar.le_eFunctional_stepCouple_idLp`,
`2^(ks) E(2^k, x)_p ≥ 2^(-1/p) 2^(k(s-1))/4`, which is unbounded for `s > 1` and bounded below by
a positive constant for `s = 1`. Its second modulus vanishes (`Haar.lpModulus_two_idLp`), so for
these `s < 1/p` the space of `Haar.memEMethod_stepCouple_iff_modulus` differs from the space
defined by the second modulus. -/
theorem not_memEMethod_stepCouple_idLp (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0) (hs : 1 ≤ s)
    (hsq : 1 < s ∨ q ≠ ∞) : ¬ (stepCouple p).MemEMethod s q (idLp p) := by
  intro hmem
  rw [InterpCouple.memEMethod_iff_eNormDyadic_lt_top (A := stepCouple p)
    InterpCouple.ofMonotoneSubgroups_norm1_zero
    (fun _ hb => InterpCouple.eq_zero_of_ofMonotoneSubgroups_norm1_lt_one hb) (by linarith)
    (Or.inl (by linarith)) hq0] at hmem
  set N := (stepCouple p).eNormDyadic s q (idLp p)
  set c := ENNReal.ofReal (1 / 2) ^ (1 / p.toReal) * ENNReal.ofReal (1 / 4)
  have hc0 : c ≠ 0 := mul_ne_zero
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (by norm_num)) ENNReal.ofReal_ne_top).ne'
    (ENNReal.ofReal_pos.2 (by norm_num)).ne'
  have hct : c ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hE : ∀ k : ℕ, c * dyadicWeight (s - 1) k ≤
      dyadicWeight s k * (stepCouple p).eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) (idLp p) := fun k => by
    have hk : ENNReal.ofReal (1 / 2 ^ k / 4) = dyadicWeight (-1) k * ENNReal.ofReal (1 / 4) := by
      rw [div_eq_mul_one_div (1 / 2 ^ k), ENNReal.ofReal_mul (by positivity), ← Real.rpow_one
        (1 / 2 ^ k), ENNReal.ofReal_one_div_two_pow_rpow]
    calc c * dyadicWeight (s - 1) k = dyadicWeight s k *
          (ENNReal.ofReal (1 / 2) ^ (1 / p.toReal) * ENNReal.ofReal (1 / 2 ^ k / 4)) := by
          rw [hk, sub_eq_add_neg, ENNReal.dyadicWeight_add]
          ring
      _ ≤ _ := by
          gcongr
          exact le_eFunctional_stepCouple_idLp hp0 hp k
  have hlq : lqNorm q (fun k : ℕ => dyadicWeight s k *
      (stepCouple p).eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) (idLp p)) ≤ N := le_add_self
  rcases hs.lt_or_eq with hs1 | rfl
  · obtain ⟨J, hJ⟩ := ENNReal.exists_dyadicWeight_neg_mul_le (sub_pos.2 hs1) hmem.ne
      (ENNReal.half_pos hc0).ne'
    have hcc : c ≤ c / 2 := calc
      c = dyadicWeight (-(s - 1)) J * (c * dyadicWeight (s - 1) J) := by
          rw [mul_left_comm, mul_comm (dyadicWeight (-(s - 1)) J),
            ENNReal.dyadicWeight_mul_neg_self, mul_one]
      _ ≤ dyadicWeight (-(s - 1)) J * N := by
          gcongr
          exact (hE J).trans ((ENNReal.le_lqNorm hq0 _ J).trans hlq)
      _ ≤ c / 2 := hJ
    exact absurd hcc (not_le.2 (ENNReal.half_lt_self hc0 hct))
  · have hq : q ≠ ∞ := hsq.resolve_left (lt_irrefl 1)
    have hconst : lqNorm q (fun _ : ℕ => c) = ∞ := by
      rw [ENNReal.lqNorm_eq_tsum hq0 hq, ENNReal.tsum_const_eq_top_of_ne_zero
        (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc0) hct).ne',
        ENNReal.top_rpow_of_pos (one_div_pos.2 (ENNReal.toReal_pos hq0 hq))]
    have hle : lqNorm q (fun _ : ℕ => c) ≤ N := (ENNReal.lqNorm_mono fun k => by
      simpa only [sub_self, ENNReal.dyadicWeight_zero_left, mul_one] using hE k).trans hlq
    exact absurd hmem (not_lt.2 (hconst ▸ hle))

end Haar

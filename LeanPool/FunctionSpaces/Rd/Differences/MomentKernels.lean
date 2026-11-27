/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Differences.DilatedDifferences
public import LeanPool.FunctionSpaces.Analysis.Differences.DomainModuli

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Moment kernels

For an integrable `g` with `∫ g = 1` and an order `L ≥ 1`, the **moment kernel** is

`m = ∑_{l=1}^L (-1)^(l+1) C(L, l) g_{1/l}`

(`Rd.momentKernel`), with the dilations `g_c = c^n g(c ·)` of `Rd.dilate`. Its dilations are
`m_c = ∑_l (-1)^(l+1) C(L, l) g_{c/l}` (`Rd.dilate_momentKernel`), and `∫ m = 1`
(`Rd.integral_momentKernel`), since `∑_{l=1}^L (-1)^(l+1) C(L, l) = 1` (`Rd.sum_jacksonCoeff`),
and `‖m‖_1 < ∞` for integrable `g` (`Rd.eLpNorm_momentKernel_ne_top`). The coefficients are
those of `-(-1)^L Δ^L` without the term `l = 0` (`Rd.neg_one_pow_mul_sum_higherDiff_coeff`), so
convolution with `m_c` averages differences of order `L`:

`f(x) - (m_c ⋆ f)(x) = (-1)^L ∫ g(z) Δ^L_{-c^(-1) z} f(x) dz`

for `f ∈ L_p` and almost every `x` (`Rd.ae_sub_conv_dilate_momentKernel_eq`; in absolute value
`Rd.ae_enorm_sub_conv_dilate_momentKernel_le`). If `g` has finite moments of the orders
`1, …, L - 1`, the moments of `m` of these orders vanish, since the coefficients satisfy
`∑_{l<L} (-1)^l C(L, l + 1) (l + 1)^j = 0` for `1 ≤ j < L` (`Rd.sum_jacksonCoeff_mul_pow`); the
estimates below go through the averaged differences instead. If `g` vanishes outside the ball of
radius `R`, then `‖f - m_c ⋆ f‖_p ≤ ‖g‖_1 ω_L(f, R/c)_p` (`Rd.enorm_sub_convLp_momentKernel_le`),
and if the steps `-c^(-1) z`, `g(z) ≠ 0`, take a set `U` into a set `T`, then
`‖1_U (f - m_c ⋆ f)‖_p ≤ ‖g‖_1 ω_L(f, R/c, T)_p`
(`Rd.eLpNorm_indicator_sub_convLp_momentKernel_le`).

In an inner product space the moment kernel of order two `m = 2 g - g_{1/2}` has vanishing first
moments, `∫ ⟪w, x⟫ m(x) dx = 0` (`Rd.integral_inner_mul_momentKernel_two`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal

namespace Rd

/-! ### The coefficients -/

/-- The coefficients `a_l = (-1)^l C(r, l + 1)`, `l < r`, of the moment kernels and of the
Jackson approximant: those of `-(-1)^r Δ^r` without its term of order `0`. -/
noncomputable def jacksonCoeff (r l : ℕ) : ℂ := (-1) ^ l * (r.choose (l + 1) : ℂ)

/-- **The coefficients of the moment kernels** are those of `(-1)^r Δ^r` without its term
`l = 0`: `(-1)^r ∑_{l ≤ r} (-1)^(r-l) C(r, l) F(l) = F(0) - ∑_{l<r} a_l F(l + 1)`. -/
theorem neg_one_pow_mul_sum_higherDiff_coeff (r : ℕ) (F : ℕ → ℂ) :
    (-1 : ℂ) ^ r * ∑ l ∈ Finset.range (r + 1), ((-1 : ℂ) ^ (r - l) * (r.choose l : ℂ)) * F l =
      F 0 - ∑ l ∈ Finset.range r, jacksonCoeff r l * F (l + 1) := by
  rw [Finset.sum_range_succ', mul_add, Finset.mul_sum, sub_eq_neg_add, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l + 1 ≤ r := Finset.mem_range.1 hl
    rw [jacksonCoeff, ← mul_assoc, ← mul_assoc, neg_one_pow_mul_neg_one_pow_sub hl', pow_succ]
    ring
  · rw [← mul_assoc, ← mul_assoc, neg_one_pow_mul_neg_one_pow_sub (Nat.zero_le r)]
    simp

/-- **The coefficients add up to `1`**: `∑_{l<r} (-1)^l C(r, l + 1) = 1` for `r ≥ 1`, since
`∑_{l ≤ r} (-1)^(r-l) C(r, l) = (1 - 1)^r = 0`. -/
theorem sum_jacksonCoeff {r : ℕ} (hr : 1 ≤ r) : ∑ l ∈ Finset.range r, jacksonCoeff r l = 1 := by
  have h0 : ∑ l ∈ Finset.range (r + 1), ((-1 : ℂ) ^ (r - l) * (r.choose l : ℂ)) = 0 := by
    have hb := add_pow (1 : ℂ) (-1) r
    rw [add_neg_cancel, zero_pow (by omega)] at hb
    rw [hb]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h := neg_one_pow_mul_sum_higherDiff_coeff r (fun _ => 1)
  simp only [mul_one] at h
  rw [h0, mul_zero] at h
  linear_combination h

/-- **Moments of the coefficients of the moment kernels**: `∑_{l<r} a_l (l + 1)^j = 0` for
`1 ≤ j < r` with `a_l = Rd.jacksonCoeff r l`. The sum is `0^j - (-1)^r Δ^r(x^j)(0)`
(`Rd.neg_one_pow_mul_sum_higherDiff_coeff`, Mathlib's `fwdDiff_iter_eq_sum_shift`), and
differences of order `r` annihilate polynomials of degree `j < r` (Mathlib's
`fwdDiff_iter_pow_eq_zero_of_lt`). -/
theorem sum_jacksonCoeff_mul_pow {r j : ℕ} (h1 : 1 ≤ j) (hj : j < r) :
    ∑ l ∈ Finset.range r, jacksonCoeff r l * ((l : ℂ) + 1) ^ j = 0 := by
  have hΔ := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℂ) hj) 0
  rw [fwdDiff_iter_eq_sum_shift] at hΔ
  simp only [zero_add, nsmul_eq_mul, mul_one, Pi.zero_apply, zsmul_eq_mul, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] at hΔ
  have h := neg_one_pow_mul_sum_higherDiff_coeff r fun l => (l : ℂ) ^ j
  rw [hΔ, mul_zero, Nat.cast_zero, zero_pow (by omega), zero_sub] at h
  push_cast at h
  linear_combination h

/-- The `L_1` norm of a function with integral `1` does not vanish. -/
theorem lintegral_enorm_ne_zero_of_integral_eq_one {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {g : α → ℂ} (hg : Integrable g ν) (h1 : ∫ x, g x ∂ν = 1) :
    ∫⁻ z, ‖g z‖ₑ ∂ν ≠ 0 := by
  intro h0
  have hae : g =ᵐ[ν] 0 := by
    have := (lintegral_eq_zero_iff' hg.aestronglyMeasurable.eNorm).1 h0
    filter_upwards [this] with z hz
    simpa using hz
  rw [integral_congr_ae hae] at h1
  simp at h1

/-! ### Moment kernels -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Dilations compose: `(Φ_d)_c = Φ_{cd}`. -/
theorem dilate_dilate (c d : ℝ) (Φ : V → ℂ) : dilate c (dilate d Φ) = dilate (c * d) Φ := by
  funext x
  simp only [dilate, smul_smul, mul_pow, Complex.ofReal_mul]
  rw [mul_comm d c]
  ring

/-- The **moment kernel** of order `L`, `m = ∑_{l=1}^L (-1)^(l+1) C(L, l) g_{1/l}`. -/
noncomputable def momentKernel (g : V → ℂ) (L : ℕ) (x : V) : ℂ :=
  ∑ l ∈ Finset.range L, jacksonCoeff L l * dilate (1 / ((l : ℝ) + 1)) g x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The dilations of the moment kernel: `m_c = ∑_{l=1}^L (-1)^(l+1) C(L, l) g_{c/l}`. -/
theorem dilate_momentKernel (c : ℝ) (g : V → ℂ) (L : ℕ) :
    dilate c (momentKernel g L) =
      fun x => ∑ l ∈ Finset.range L, jacksonCoeff L l * dilate (c / ((l : ℝ) + 1)) g x := by
  funext x
  have h : ∀ l : ℕ, dilate (c / ((l : ℝ) + 1)) g x =
      dilate c (dilate (1 / ((l : ℝ) + 1)) g) x := fun l => by
    rw [dilate_dilate, mul_one_div]
  simp only [h]
  simp only [dilate, momentKernel, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Moment kernels of integrable functions are integrable. -/
theorem integrable_momentKernel {g : V → ℂ} (hg : Integrable g μ) (L : ℕ) :
    Integrable (momentKernel g L) μ :=
  integrable_finsetSum _ fun l _ => (integrable_dilate hg (by positivity)).const_mul _

/-- **Moment kernels have a finite `L_1` norm**: `‖m‖_1 ≠ ∞` for the moment kernel `m` of an
integrable `g` (`Rd.integrable_momentKernel`). -/
theorem eLpNorm_momentKernel_ne_top {g : V → ℂ} (hg : Integrable g μ) (L : ℕ) :
    eLpNorm (momentKernel g L) 1 μ ≠ ∞ :=
  (memLp_one_iff_integrable.2 (integrable_momentKernel hg L)).eLpNorm_ne_top

/-- `‖m‖_1 < ∞` for the moment kernel `m` of an integrable `g`
(`Rd.eLpNorm_momentKernel_ne_top`). -/
theorem eLpNorm_momentKernel_lt_top {g : V → ℂ} (hg : Integrable g μ) (L : ℕ) :
    eLpNorm (momentKernel g L) 1 μ < ∞ :=
  (eLpNorm_momentKernel_ne_top hg L).lt_top

/-- **The moment kernel has integral `1`**: `∫ m = ∑_{l=1}^L (-1)^(l+1) C(L, l) ∫ g = 1`. -/
theorem integral_momentKernel {g : V → ℂ} (hg : Integrable g μ) (h1 : ∫ x, g x ∂μ = 1)
    {L : ℕ} (hL : 1 ≤ L) : ∫ x, momentKernel g L x ∂μ = 1 := by
  simp only [momentKernel]
  rw [integral_finsetSum _ fun l _ => (integrable_dilate hg (by positivity)).const_mul _]
  rw [← sum_jacksonCoeff hL]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_dilate g (by positivity), h1, mul_one]

/-- **Convolution is linear in the kernel** almost everywhere:
`(∑_i a_i K_i) ⋆ f = ∑_i a_i (K_i ⋆ f)` for integrable `K_i` and `f ∈ L_p`. -/
theorem conv_finsetSum_kernel_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {ι : Type*}
    (s : Finset ι) (a : ι → ℂ) {K : ι → V → ℂ} (hK : ∀ i ∈ s, Integrable (K i) μ) {f : V → ℂ}
    (hf : MemLp f p μ) :
    conv (fun x => ∑ i ∈ s, a i * K i x) f μ =ᵐ[μ] fun x => ∑ i ∈ s, a i * conv (K i) f μ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine Filter.EventuallyEq.of_eq (funext fun x => ?_)
    simp [conv_apply]
  | insert i s hi ih =>
    have hKi : Integrable (fun x => a i * K i x) μ :=
      (hK i (Finset.mem_insert_self i s)).const_mul _
    have hKs : Integrable (fun x => ∑ j ∈ s, a j * K j x) μ :=
      integrable_finsetSum _ fun j hj => (hK j (Finset.mem_insert_of_mem hj)).const_mul _
    have hsplit : (fun x => ∑ j ∈ insert i s, a j * K j x) =
        (fun x => a i * K i x) + fun x => ∑ j ∈ s, a j * K j x := by
      funext x
      simp [Finset.sum_insert hi]
    have hsm : conv (fun x => a i * K i x) f μ = fun x => a i * conv (K i) f μ x :=
      smul_conv (K i) f (a i)
    rw [hsplit]
    filter_upwards [add_conv_ae hp1 hp hKi hKs hf,
      ih fun j hj => hK j (Finset.mem_insert_of_mem hj)] with x h1 h2
    rw [h1, Pi.add_apply, h2, hsm, Finset.sum_insert hi]

/-- **Averaged differences** (the identity behind the moment kernels and the Jackson
approximant): for an integrable `g` with `∫ g = 1`, `f ∈ L_p`, `c > 0` and almost every `x`,
`f(x) - ∑_{l=1}^L (-1)^(l+1) C(L, l) (g_{c/l} ⋆ f)(x) = (-1)^L ∫ g(z) Δ^L_{-c^(-1) z} f(x) dz`. -/
theorem ae_sub_sum_conv_dilate_eq {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {g f : V → ℂ}
    (hg : Integrable g μ) (h1 : ∫ x, g x ∂μ = 1) (hf : MemLp f p μ) (L : ℕ) {c : ℝ}
    (hc : 0 < c) :
    ∀ᵐ x ∂μ, f x - ∑ l ∈ Finset.range L,
        jacksonCoeff L l * conv (dilate (c / ((l : ℝ) + 1)) g) f μ x =
      ∫ z, g z * ((-1 : ℂ) ^ L * (fwdDiff (-c⁻¹ • z))^[L] f x) ∂μ := by
  have hcl : ∀ l : ℕ, 0 < c / ((l : ℝ) + 1) := fun l => by positivity
  have hint : ∀ᵐ x ∂μ, ∀ l ∈ Finset.range L,
      Integrable (fun z => g z * f (x - (c / ((l : ℝ) + 1))⁻¹ • z)) μ :=
    (Filter.eventually_all_finset _).2 fun l _ => ae_integrable_dilate_mul hp1 hp hg hf (hcl l)
  have hsmul : ∀ (z : V) (l : ℕ), ((l + 1 : ℕ) : ℝ) • (-c⁻¹ • z) =
      -((c / ((l : ℝ) + 1))⁻¹ • z) := fun z l => by
    rw [inv_div, smul_smul, mul_neg, neg_smul, div_eq_mul_inv, Nat.cast_succ]
  filter_upwards [hint] with x h3
  have hexp : ∀ z, (-1 : ℂ) ^ L * (fwdDiff (-c⁻¹ • z))^[L] f x =
      f x - ∑ l ∈ Finset.range L, jacksonCoeff L l * f (x - (c / ((l : ℝ) + 1))⁻¹ • z) :=
    fun z => by
      rw [higherDiff_apply, neg_one_pow_mul_sum_higherDiff_coeff]
      congr 1
      · simp
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [hsmul z l, ← sub_eq_add_neg]
  have hsum : ∑ l ∈ Finset.range L,
      jacksonCoeff L l * conv (dilate (c / ((l : ℝ) + 1)) g) f μ x =
      ∑ l ∈ Finset.range L,
        ∫ z, jacksonCoeff L l * (g z * f (x - (c / ((l : ℝ) + 1))⁻¹ • z)) ∂μ :=
    Finset.sum_congr rfl fun l _ => by
      rw [conv_dilate_apply _ _ (hcl l), integral_const_mul]
  have hf0 : f x = ∫ z, g z * f x ∂μ := by rw [integral_mul_const, h1, one_mul]
  rw [hsum, hf0, ← integral_finsetSum _ fun l hl => (h3 l hl).const_mul _,
    ← integral_sub (hg.mul_const _) (integrable_finsetSum _ fun l hl => (h3 l hl).const_mul _)]
  congr 1
  funext z
  rw [hexp z, mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **Convolution with a moment kernel averages differences**: for an integrable `g` with
`∫ g = 1`, `f ∈ L_p`, `c > 0` and almost every `x`,
`f(x) - (m_c ⋆ f)(x) = (-1)^L ∫ g(z) Δ^L_{-c^(-1) z} f(x) dz`. -/
theorem ae_sub_conv_dilate_momentKernel_eq {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {g f : V → ℂ}
    (hg : Integrable g μ) (h1 : ∫ x, g x ∂μ = 1) (hf : MemLp f p μ) (L : ℕ) {c : ℝ}
    (hc : 0 < c) :
    ∀ᵐ x ∂μ, f x - conv (dilate c (momentKernel g L)) f μ x =
      ∫ z, g z * ((-1 : ℂ) ^ L * (fwdDiff (-c⁻¹ • z))^[L] f x) ∂μ := by
  rw [dilate_momentKernel]
  filter_upwards [conv_finsetSum_kernel_ae hp1 hp (Finset.range L) (jacksonCoeff L)
    (K := fun l => dilate (c / ((l : ℝ) + 1)) g) (fun l _ => integrable_dilate hg (by positivity))
    hf,
    ae_sub_sum_conv_dilate_eq hp1 hp hg h1 hf L hc] with x h2 h3
  rw [h2]
  exact h3

/-- **The averaged differences, in absolute value**: for an integrable `g` with `∫ g = 1`,
`f ∈ L_p` with `1 ≤ p < ∞`, `c > 0` and almost every `x`,
`|f(x) - (m_c ⋆ f)(x)| ≤ ∫ |g(z)| |Δ^L_{-c^(-1) z} f(x)| dz`, where `m` is the moment kernel of
order `L` of `g`. -/
theorem ae_enorm_sub_conv_dilate_momentKernel_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {g f : V → ℂ} (hg : Integrable g μ) (h1 : ∫ x, g x ∂μ = 1) (hf : MemLp f p μ) (L : ℕ)
    {c : ℝ} (hc : 0 < c) :
    ∀ᵐ x ∂μ, ‖f x - conv (dilate c (momentKernel g L)) f μ x‖ₑ ≤
      ∫⁻ z, ‖g z‖ₑ * ‖(fwdDiff (-c⁻¹ • z))^[L] f x‖ₑ ∂μ := by
  filter_upwards [ae_sub_conv_dilate_momentKernel_eq hp1 hp hg h1 hf L hc] with x hx
  rw [hx]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq (lintegral_congr fun z => ?_))
  rw [eNorm_mul, eNorm_mul, eNorm_pow, eNorm_neg, eNorm_one, one_pow, one_mul]

/-- **Moment kernels approximate with the modulus on a set**: let `g` have integral `1` and vanish
outside the ball of radius `R`, and let `U` be a measurable set that the steps of the averaged
differences take into a measurable set `T`, `U ⊆ T_{L h}` for `h = -c^(-1) z` and
`g(z) ≠ 0`. Then `‖1_U (f - m_c ⋆ f)‖_p ≤ ‖g‖_1 ω_L(f, R/c, T)_p`, by the averaged differences
and the weighted Jensen inequality. -/
theorem eLpNorm_indicator_sub_convLp_momentKernel_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {g : V → ℂ} (hg : Integrable g μ) (h1 : ∫ x, g x ∂μ = 1) {R : ℝ}
    (hgR : ∀ z, R < ‖z‖ → g z = 0) (L : ℕ) {c : ℝ} (hc : 0 < c) {U : Set V}
    (hU : MeasurableSet U) {T : Set V} (hstep : ∀ z, g z ≠ 0 → U ⊆ stepSet T L (-c⁻¹ • z))
    (f : Lp ℂ p μ) :
    eLpNorm (U.indicator
        ⇑(f - convLp hp (integrable_dilate (integrable_momentKernel hg L) hc.ne') f)) p μ ≤
      (∫⁻ z, ‖g z‖ₑ ∂μ) * modulusOn μ T L p (f : V → ℂ) (R / c) := by
  have hp1 : 1 ≤ p := Fact.out
  have hfm : Measurable (f : V → ℂ) := (Lp.stronglyMeasurable f).measurable
  set ω := modulusOn μ T L p (f : V → ℂ) (R / c)
  set G : V → V → ℂ := fun x z =>
    U.indicator (fun x => (-1 : ℂ) ^ L * (fwdDiff (-c⁻¹ • z))^[L] (f : V → ℂ) x) x with hGdef
  have hG : Measurable (Function.uncurry G) := by
    have heq : Function.uncurry G = (U ×ˢ Set.univ).indicator fun y : V × V =>
        (-1 : ℂ) ^ L * ∑ l ∈ Finset.range (L + 1), ((-1 : ℂ) ^ (L - l) * (L.choose l : ℂ)) *
          (f : V → ℂ) (y.1 + (l : ℝ) • (-c⁻¹ • y.2)) := by
      funext y
      rcases y with ⟨x, z⟩
      by_cases hx : x ∈ U
      · rw [Function.uncurry_apply_pair,
          Set.indicator_of_mem (Set.mk_mem_prod hx (Set.mem_univ z))]
        simp only [G, Set.indicator_of_mem hx]
        exact congrArg _ (higherDiff_apply L (-c⁻¹ • z) _ x)
      · rw [Function.uncurry_apply_pair,
          Set.indicator_of_notMem fun h => hx (Set.mem_prod.1 h).1]
        simp only [G, Set.indicator_of_notMem hx]
    rw [heq]
    exact (measurable_const.mul (Finset.measurable_sum _ fun l _ => measurable_const.mul
      (hfm.comp (measurable_fst.add ((measurable_snd.const_smul _).const_smul _))))).indicator
      (hU.prod MeasurableSet.univ)
  have hae : U.indicator
      ⇑(f - convLp hp (integrable_dilate (integrable_momentKernel hg L) hc.ne') f) =ᵐ[μ]
      fun x => ∫ z, g z * G x z ∂μ := by
    filter_upwards [Lp.coeFn_sub f (convLp hp (integrable_dilate (integrable_momentKernel hg L)
        hc.ne') f), convLp_apply_ae hp (integrable_dilate (integrable_momentKernel hg L)
        hc.ne') f, ae_sub_conv_dilate_momentKernel_eq hp1 hp hg h1 (Lp.memLp f) L hc]
      with x h1' h2 h3
    by_cases hx : x ∈ U
    · simp only [G, Set.indicator_of_mem hx]
      rw [h1', Pi.sub_apply, h2]
      exact h3
    · simp [G, Set.indicator_of_notMem hx]
  have hbound : ∀ z, g z ≠ 0 → eLpNorm (fun x => G x z) p μ ≤ ω := fun z hz => by
    have hzR : ‖z‖ ≤ R := not_lt.1 fun h => hz (hgR z h)
    have hnorm : ‖-c⁻¹ • z‖ ≤ R / c := by
      rw [norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg hc.le, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hzR hc.le
    have hD := (aestronglyMeasurable_higherDiff (Lp.aestronglyMeasurable f) L
      (-c⁻¹ • z)).indicator hU
    have heq : eLpNorm (fun x => G x z) p μ =
        eLpNorm (U.indicator ((fwdDiff (-c⁻¹ • z))^[L] (f : V → ℂ))) p μ := by
      refine eLpNorm_congr_norm_ae ((hG.comp measurable_prodMk_right).aestronglyMeasurable)
        hD (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ U
      · simp [G, Set.indicator_of_mem hx]
      · simp [G, Set.indicator_of_notMem hx]
    calc eLpNorm (fun x => G x z) p μ
        = eLpNorm (U.indicator ((fwdDiff (-c⁻¹ • z))^[L] (f : V → ℂ))) p μ := heq
      _ ≤ eLpNorm ((stepSet T L (-c⁻¹ • z)).indicator
            ((fwdDiff (-c⁻¹ • z))^[L] (f : V → ℂ))) p μ :=
          eLpNorm_mono hD fun x => norm_indicator_le_of_subset (hstep z hz) _ x
      _ ≤ ω := eLpNorm_indicator_higherDiff_le_modulusOn hnorm
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_integral_kernel_le_of_bound hp1 hp hg.aestronglyMeasurable
    (lintegral_enorm_ne_zero_of_integral_eq_one hg h1) hg.2.ne hG hbound

/-- **Moment kernels approximate with the modulus of smoothness**: if `g` has integral `1` and
vanishes outside the ball of radius `R`, then `‖f - m_c ⋆ f‖_p ≤ ‖g‖_1 ω_L(f, R/c)_p` (the case
`U = V` of `Rd.eLpNorm_indicator_sub_convLp_momentKernel_le`). -/
theorem enorm_sub_convLp_momentKernel_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {g : V → ℂ}
    (hg : Integrable g μ) (h1 : ∫ x, g x ∂μ = 1) {R : ℝ} (hgR : ∀ z, R < ‖z‖ → g z = 0)
    (L : ℕ) {c : ℝ} (hc : 0 < c) (f : Lp ℂ p μ) :
    ‖f - convLp hp (integrable_dilate (integrable_momentKernel hg L) hc.ne') f‖ₑ ≤
      (∫⁻ z, ‖g z‖ₑ ∂μ) * modulus μ L p (f : V → ℂ) (R / c) := by
  have h := eLpNorm_indicator_sub_convLp_momentKernel_le hp hg h1 hgR L hc MeasurableSet.univ
    (T := Set.univ) (fun _ _ => by rw [stepSet_univ]) f
  rwa [Set.indicator_univ, modulusOn_univ, ← Lp.eNorm_def] at h

end Rd

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

/-! ### First moments of the moment kernels of order two -/

/-- **The moment kernel of order two has vanishing first moments**: for
`m = 2 g - g_{1/2}` (`Rd.momentKernel g 2`) and every `w`, `∫ ⟪w, x⟫ m(x) dx = 0`, since the first
moment of `g_c` is `c⁻¹` times that of `g` (`Rd.integral_inner_mul_dilate`). -/
theorem integral_inner_mul_momentKernel_two {g : V → ℂ} (w : V)
    (hg : Integrable (fun x => (inner ℝ w x : ℂ) * g x) μ) :
    ∫ x, (inner ℝ w x : ℂ) * momentKernel g 2 x ∂μ = 0 := by
  have hint : ∀ {c : ℝ}, c ≠ 0 → Integrable (fun x => (inner ℝ w x : ℂ) * dilate c g x) μ :=
    fun hc => by
      simp_rw [inner_mul_dilate_eq g w hc]
      exact (integrable_dilate hg hc).const_mul _
  have hpt : ∀ x, (inner ℝ w x : ℂ) * momentKernel g 2 x =
      2 * ((inner ℝ w x : ℂ) * dilate 1 g x) - (inner ℝ w x : ℂ) * dilate (1 / 2) g x :=
    fun x => by
      simp [momentKernel, Finset.sum_range_succ, jacksonCoeff, one_add_one_eq_two]
      ring
  simp_rw [hpt]
  rw [integral_sub ((hint one_ne_zero).const_mul _) (hint (by norm_num)), integral_const_mul,
    integral_inner_mul_dilate g w one_pos,
    integral_inner_mul_dilate g w (by norm_num : (0 : ℝ) < 1 / 2)]
  push_cast
  ring

end Rd

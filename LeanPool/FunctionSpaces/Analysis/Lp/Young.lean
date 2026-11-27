/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Lp.LintegralForm
public import TauCeti.Analysis.Convolution.Young
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Prod

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Young's inequality on measurable groups

On a measurable group `G` with a right-invariant s-finite measure `μ` (a Haar measure on `ℝ^d` or
on the torus), the convolution `(K ⋆ f)(x) = ∫ K(y) f(x - y) dμ(y)` with the multiplication of
`ℂ` satisfies **Young's inequality** `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p` for `1 ≤ p ≤ ∞`
(`MeasureTheory.eLpNorm_complexConvolution_le`). For finite `p`, the integral estimate below uses
the weighted Jensen inequality

`(∫ a g)^p ≤ (∫ a)^(p-1) ∫ a g^p`

(`MeasureTheory.lintegral_mul_rpow_le`, Hölder's inequality for the measure `a dμ`). Integrated
over `x` by Tonelli's theorem, it gives `∫ (∫ a(y) K(x, y) dy)^q dx ≤ (∫ a)^q C` for every kernel
with `∫ K(x, y)^q dx ≤ C` for all `y` (`MeasureTheory.lintegral_rpow_lintegral_kernel_le`). For
`K(x, y) = |f(x - y)|` the invariance of `μ` gives Young's inequality
(`MeasureTheory.lintegral_rpow_lintegral_le`). The same bound shows that the convolution integral
converges absolutely almost everywhere (`MeasureTheory.ae_convolutionExistsAt`). Mathlib has the
pointwise bounds of convolutions, not Young's inequality.

**Weighted averages** (Minkowski's integral inequality in the form of the weighted Jensen
inequality): for a weight `Φ` on a second measure space,
`‖∫ Φ(z) G(·, z) dz‖_p^p ≤ ‖Φ‖_1^(p-1) ∫ |Φ(z)| ‖G(·, z)‖_p^p dz`
(`MeasureTheory.eLpNorm_integral_kernel_le`).
-/

@[expose] public section

open scoped ENNReal Convolution

namespace MeasureTheory

/-! ### The weighted Jensen inequality -/

/-- **Weighted Jensen inequality**: for `1 ≤ p` and nonnegative `a`, `g`,
`(∫ a g)^p ≤ (∫ a)^(p-1) ∫ a g^p`. This is Hölder's inequality for the measure `a dμ`: split
`a g = a^(1/q) (a^(1/p) g)` with the conjugate exponent `q` (Mathlib's
`ENNReal.lintegral_mul_le_Lp_mul_Lq`). -/
theorem lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    (hp : 1 ≤ p) {a g : α → ℝ≥0∞} (ha : AEMeasurable a μ) (hg : AEMeasurable g μ) :
    (∫⁻ y, a y * g y ∂μ) ^ p ≤ (∫⁻ y, a y ∂μ) ^ (p - 1) * ∫⁻ y, a y * g y ^ p ∂μ := by
  rcases eq_or_lt_of_le hp with rfl | hp1
  · simp
  set q := p.conjExponent
  have hpq : p.HolderConjugate q := .conjExponent hp1
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := hpq.symm.pos
  have hsum : 1 / q + 1 / p = 1 := by
    have := hpq.inv_add_inv_eq_one
    rw [one_div, one_div]
    linarith
  have hsplit : ∀ y, a y * g y = a y ^ (1 / q) * (a y ^ (1 / p) * g y) := fun y => by
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hsum,
      ENNReal.rpow_one]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq.symm (ha.pow_const (1 / q))
    ((ha.pow_const (1 / p)).mul hg)
  have h1 : ∀ y, (a y ^ (1 / q)) ^ q = a y := fun y => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have h2 : ∀ y, (a y ^ (1 / p) * g y) ^ p = a y * g y ^ p := fun y => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
      ENNReal.rpow_one]
  simp only [Pi.mul_apply, h1, h2] at hH
  have hexp : 1 / q * p = p - 1 := by
    have h : 1 / q = 1 - 1 / p := by linarith
    rw [h]
    field_simp
  calc (∫⁻ y, a y * g y ∂μ) ^ p
      = (∫⁻ y, a y ^ (1 / q) * (a y ^ (1 / p) * g y) ∂μ) ^ p := by
        rw [lintegral_congr fun y => hsplit y]
    _ ≤ ((∫⁻ y, a y ∂μ) ^ (1 / q) * (∫⁻ y, a y * g y ^ p ∂μ) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow hH hp0.le
    _ = (∫⁻ y, a y ∂μ) ^ (p - 1) * ∫⁻ y, a y * g y ^ p ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel hp0.ne', ENNReal.rpow_one, hexp]

/-- **Young's inequality for kernels**, for nonnegative functions: for `1 ≤ q`, s-finite measures
`μ` on `X` and `ν` on `Y`, an almost everywhere measurable `a : Y → [0, ∞]` and a jointly almost
everywhere measurable `K : X × Y → [0, ∞]` with `∫ K(x, y)^q dμ(x) ≤ C` for every `y`,
`∫ (∫ a(y) K(x, y) dν(y))^q dμ(x) ≤ (∫ a dν)^q C`. By the weighted Jensen inequality the inner
power is at most `(∫ a)^(q-1) ∫ a(y) K(x, y)^q dν(y)`, and Tonelli's theorem gives
`(∫ a)^(q-1) ∫ a(y) C dν(y)`. -/
theorem lintegral_rpow_lintegral_kernel_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] {q : ℝ} (hq1 : 1 ≤ q)
    {a : Y → ℝ≥0∞} (ha : AEMeasurable a ν) {K : X → Y → ℝ≥0∞}
    (hK : AEMeasurable (Function.uncurry K) (μ.prod ν)) {C : ℝ≥0∞}
    (hC : ∀ y, ∫⁻ x, K x y ^ q ∂μ ≤ C) :
    ∫⁻ x, (∫⁻ y, a y * K x y ∂ν) ^ q ∂μ ≤ (∫⁻ y, a y ∂ν) ^ q * C := by
  have hprod : AEMeasurable (Function.uncurry fun x y => a y * K x y ^ q) (μ.prod ν) :=
    ha.comp_snd.mul (hK.pow_const q)
  have hx : ∀ᵐ x ∂μ, AEMeasurable (K x) ν :=
    hK.aestronglyMeasurable.prodMk_left.mono fun x hx => hx.aemeasurable
  have hy : ∀ᵐ y ∂ν, AEMeasurable (fun x => K x y ^ q) μ :=
    hK.prod_swap.aestronglyMeasurable.prodMk_left.mono fun y hy => hy.aemeasurable.pow_const q
  calc ∫⁻ x, (∫⁻ y, a y * K x y ∂ν) ^ q ∂μ
      ≤ ∫⁻ x, (∫⁻ y, a y ∂ν) ^ (q - 1) * ∫⁻ y, a y * K x y ^ q ∂ν ∂μ :=
        lintegral_mono_ae (hx.mono fun x hx => lintegral_mul_rpow_le hq1 ha hx)
    _ = (∫⁻ y, a y ∂ν) ^ (q - 1) * ∫⁻ x, ∫⁻ y, a y * K x y ^ q ∂ν ∂μ :=
        lintegral_const_mul'' _ hprod.lintegral_prod_right'
    _ = (∫⁻ y, a y ∂ν) ^ (q - 1) * ∫⁻ y, ∫⁻ x, a y * K x y ^ q ∂μ ∂ν := by
        rw [lintegral_lintegral_swap hprod]
    _ ≤ (∫⁻ y, a y ∂ν) ^ (q - 1) * ∫⁻ y, a y * C ∂ν := by
        gcongr 1
        refine lintegral_mono_ae (hy.mono fun y hy => ?_)
        rw [lintegral_const_mul'' _ hy]
        gcongr
        exact hC y
    _ = (∫⁻ y, a y ∂ν) ^ q * C := by
        rw [lintegral_mul_const'' _ ha, ← mul_assoc]
        congr 1
        conv_rhs => rw [show q = (q - 1) + 1 by ring]
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]

/-! ### Young's inequality -/

section Young

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]

/-- **The integral form of Young's inequality** for nonnegative functions: for `1 ≤ q`,
`∫ (∫ a(y) b(x - y) dy)^q dx ≤ (∫ a)^q ∫ b^q`. This is the kernel form
`MeasureTheory.lintegral_rpow_lintegral_kernel_le` for `K(x, y) = b(x - y)`, since
`∫ b(x - y)^q dx = ∫ b^q` by the invariance of `μ`. -/
theorem lintegral_rpow_lintegral_mul_le {q : ℝ} (hq1 : 1 ≤ q) {a b : G → ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    ∫⁻ x, (∫⁻ y, a y * b (x - y) ∂μ) ^ q ∂μ ≤ (∫⁻ y, a y ∂μ) ^ q * ∫⁻ x, b x ^ q ∂μ :=
  lintegral_rpow_lintegral_kernel_le hq1 ha (K := fun x y => b (x - y))
    (hb.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant μ μ))
    fun y => (lintegral_sub_right_eq_self (fun x => b x ^ q) y).le

/-- The integrand of `x ↦ ∫ |K(y)| |f(x - y)|^q dy` is measurable on the product. -/
theorem aemeasurable_kernel_rpow {K f : G → ℂ} (hK : AEStronglyMeasurable K μ)
    (hf : AEStronglyMeasurable f μ) (q : ℝ) :
    AEMeasurable (Function.uncurry fun x y => ‖K y‖ₑ * ‖f (x - y)‖ₑ ^ q) (μ.prod μ) :=
  hK.eNorm.comp_snd.mul ((hf.eNorm.pow_const q).comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub_of_right_invariant μ μ))

/-- The function `x ↦ ∫ |K(y)| |f(x - y)| dy` is measurable. -/
theorem aemeasurable_lintegral_kernel {K f : G → ℂ} (hK : AEStronglyMeasurable K μ)
    (hf : AEStronglyMeasurable f μ) :
    AEMeasurable (fun x => ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ) μ := by
  have h := (aemeasurable_kernel_rpow hK hf 1).lintegral_prod_right'
  simpa only [ENNReal.rpow_one, Function.uncurry_apply_pair] using h

/-- **The integral form of Young's inequality**: for `1 ≤ p < ∞`,
`∫ (∫ |K(y)| |f(x - y)| dy)^p dx ≤ (‖K‖_1 ‖f‖_p)^p`. -/
theorem lintegral_rpow_lintegral_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f : G → ℂ}
    (hK : AEStronglyMeasurable K μ) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, (∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ) ^ p.toReal ∂μ ≤
      (eLpNorm K 1 μ * eLpNorm f p μ) ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq1 : 1 ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp hp1
    rwa [ENNReal.toReal_one] at h
  refine (lintegral_rpow_lintegral_mul_le hq1 hK.eNorm hf.eNorm).trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), eLpNorm_one_eq_lintegral_eNorm hK,
    eLpNorm_rpow_eq hf hp0 hp]

/-- Young's inequality for complex-valued convolution with an integrable kernel. -/
theorem eLpNorm_complexConvolution_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K f : G → ℂ}
    (hK : AEStronglyMeasurable K μ) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (K ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] f) p μ ≤ eLpNorm K 1 μ * eLpNorm f p μ := by
  have hmul : ‖ContinuousLinearMap.mul ℂ ℂ‖ₑ = 1 := by
    rw [← ofReal_norm, ContinuousLinearMap.opNorm_mul, ENNReal.ofReal_one]
  simpa only [hmul, one_mul] using eLpNorm_convolution_le (ContinuousLinearMap.mul ℂ ℂ) hK hf hp1

/-- The convolution of an integrable kernel with an `L_p` function is in `L_p`. -/
theorem memLp_convolution {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K f : G → ℂ}
    (hK : Integrable K μ) (hf : MemLp f p μ) :
    MemLp (K ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] f) p μ :=
  lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (ENNReal.mul_ne_top
    (memLp_one_iff_integrable.2 hK).eLpNorm_ne_top hf.eLpNorm_ne_top)
    (eLpNorm_complexConvolution_le hp1 hK.aestronglyMeasurable hf.aestronglyMeasurable))

/-- **The convolution integral converges absolutely almost everywhere** for an integrable
kernel and `f ∈ L_p`, `1 ≤ p < ∞`: the integral form of Young's inequality is finite. -/
theorem ae_convolutionExistsAt {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f : G → ℂ}
    (hK : Integrable K μ) (hf : MemLp f p μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt K f x (ContinuousLinearMap.mul ℂ ℂ) μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hK1 : eLpNorm K 1 μ ≠ ∞ := (memLp_one_iff_integrable.2 hK).eLpNorm_ne_top
  have hfin : ∫⁻ x, (∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ) ^ p.toReal ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le (ENNReal.mul_ne_top hK1
      hf.eLpNorm_ne_top))
      (lintegral_rpow_lintegral_le hp1 hp hK.aestronglyMeasurable hf.aestronglyMeasurable)
  have hmeas : AEMeasurable (fun x => (∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ) ^ p.toReal) μ :=
    (aemeasurable_lintegral_kernel hK.aestronglyMeasurable hf.aestronglyMeasurable).pow_const _
  filter_upwards [ae_lt_top' hmeas hfin] with x hx
  have hx' : ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ < ∞ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.top_rpow_of_pos hq] at hx
    exact lt_irrefl _ hx
  refine ⟨hK.aestronglyMeasurable.convolution_integrand_snd (ContinuousLinearMap.mul ℂ ℂ)
    hf.aestronglyMeasurable x, ?_⟩
  simpa [HasFiniteIntegral, eNorm_mul] using hx'

end Young

/-! ### Weighted averages -/

section Average

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SFinite μ] [SFinite ν]

/-- **Weighted averages in `L_p`** (Minkowski's integral inequality, in the form of the weighted
Jensen inequality): for `1 ≤ p < ∞`, a weight `Φ` on `β` and a jointly measurable `G`,
`‖∫ Φ(z) G(·, z) dν(z)‖_p^p ≤ ‖Φ‖_1^(p-1) ∫ |Φ(z)| ‖G(·, z)‖_p^p dν(z)`. -/
theorem eLpNorm_integral_kernel_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Φ : β → ℂ}
    (hΦ : AEStronglyMeasurable Φ ν) {G : α → β → ℂ} (hG : Measurable (Function.uncurry G)) :
    eLpNorm (fun x => ∫ z, Φ z * G x z ∂ν) p μ ^ p.toReal ≤
      (∫⁻ z, ‖Φ z‖ₑ ∂ν) ^ (p.toReal - 1) *
        ∫⁻ z, ‖Φ z‖ₑ * eLpNorm (fun x => G x z) p μ ^ p.toReal ∂ν := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp hp1
    rwa [ENNReal.toReal_one] at h
  have hprod : AEMeasurable (Function.uncurry fun x z => ‖Φ z‖ₑ * ‖G x z‖ₑ ^ p.toReal)
      (μ.prod ν) :=
    hΦ.eNorm.comp_snd.mul (hG.eNorm.pow_const _).aemeasurable
  have hint : AEStronglyMeasurable (fun x => ∫ z, Φ z * G x z ∂ν) μ :=
    (hΦ.comp_snd.mul hG.aestronglyMeasurable).integral_prod_right'
  rw [eLpNorm_rpow_eq hint hp0 hp]
  calc ∫⁻ x, ‖∫ z, Φ z * G x z ∂ν‖ₑ ^ p.toReal ∂μ
      ≤ ∫⁻ x, (∫⁻ z, ‖Φ z‖ₑ * ‖G x z‖ₑ ∂ν) ^ p.toReal ∂μ := lintegral_mono fun x => by
        refine ENNReal.rpow_le_rpow ((eNorm_integral_le_lintegral_eNorm _).trans_eq ?_) hq.le
        simp_rw [eNorm_mul]
    _ ≤ ∫⁻ x, (∫⁻ z, ‖Φ z‖ₑ ∂ν) ^ (p.toReal - 1) *
          ∫⁻ z, ‖Φ z‖ₑ * ‖G x z‖ₑ ^ p.toReal ∂ν ∂μ :=
        lintegral_mono fun x => lintegral_mul_rpow_le hq1 hΦ.eNorm
          (hG.comp measurable_prodMk_left).eNorm.aemeasurable
    _ = (∫⁻ z, ‖Φ z‖ₑ ∂ν) ^ (p.toReal - 1) *
          ∫⁻ x, ∫⁻ z, ‖Φ z‖ₑ * ‖G x z‖ₑ ^ p.toReal ∂ν ∂μ :=
        lintegral_const_mul'' _ hprod.lintegral_prod_right'
    _ = (∫⁻ z, ‖Φ z‖ₑ ∂ν) ^ (p.toReal - 1) *
          ∫⁻ z, ∫⁻ x, ‖Φ z‖ₑ * ‖G x z‖ₑ ^ p.toReal ∂μ ∂ν := by
        rw [lintegral_lintegral_swap hprod]
    _ = (∫⁻ z, ‖Φ z‖ₑ ∂ν) ^ (p.toReal - 1) *
          ∫⁻ z, ‖Φ z‖ₑ * eLpNorm (fun x => G x z) p μ ^ p.toReal ∂ν := by
        congr 1
        refine lintegral_congr fun z => ?_
        have hGz : AEStronglyMeasurable (fun x => G x z) μ :=
          (hG.comp measurable_prodMk_right).aestronglyMeasurable
        rw [lintegral_const_mul' _ _ eNorm_ne_top, eLpNorm_rpow_eq hGz hp0 hp]

/-- **Weighted averages of uniformly bounded functions**: if `‖G(·, z)‖_p ≤ M` for every `z` with
`Φ(z) ≠ 0` and `0 < ‖Φ‖_1 < ∞`, then `‖∫ Φ(z) G(·, z) dν(z)‖_p ≤ ‖Φ‖_1 M`
(`MeasureTheory.eLpNorm_integral_kernel_le`). -/
theorem eLpNorm_integral_kernel_le_of_bound {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Φ : β → ℂ}
    (hΦ : AEStronglyMeasurable Φ ν) (hΦ0 : ∫⁻ z, ‖Φ z‖ₑ ∂ν ≠ 0) (hΦt : ∫⁻ z, ‖Φ z‖ₑ ∂ν ≠ ∞)
    {G : α → β → ℂ} (hG : Measurable (Function.uncurry G)) {M : ℝ≥0∞}
    (hM : ∀ z, Φ z ≠ 0 → eLpNorm (fun x => G x z) p μ ≤ M) :
    eLpNorm (fun x => ∫ z, Φ z * G x z ∂ν) p μ ≤ (∫⁻ z, ‖Φ z‖ₑ ∂ν) * M := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [← ENNReal.rpow_le_rpow_iff hq]
  refine (eLpNorm_integral_kernel_le hp1 hp hΦ hG).trans ?_
  calc (∫⁻ z, ‖Φ z‖ₑ ∂ν) ^ (p.toReal - 1) *
        ∫⁻ z, ‖Φ z‖ₑ * eLpNorm (fun x => G x z) p μ ^ p.toReal ∂ν
      ≤ (∫⁻ z, ‖Φ z‖ₑ ∂ν) ^ (p.toReal - 1) * ∫⁻ z, ‖Φ z‖ₑ * M ^ p.toReal ∂ν :=
        mul_le_mul' le_rfl (lintegral_mono fun z => by
          by_cases hz : Φ z = 0
          · simp [hz]
          · exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hM z hz) hq.le))
    _ = (∫⁻ z, ‖Φ z‖ₑ ∂ν) ^ (p.toReal - 1) * (∫⁻ z, ‖Φ z‖ₑ ∂ν) ^ (1 : ℝ) * M ^ p.toReal := by
        rw [lintegral_mul_const'' _ hΦ.eNorm, ENNReal.rpow_one, mul_assoc]
    _ = ((∫⁻ z, ‖Φ z‖ₑ ∂ν) * M) ^ p.toReal := by
        rw [← ENNReal.rpow_add _ _ hΦ0 hΦt, sub_add_cancel, ENNReal.mul_rpow_of_nonneg _ _ hq.le]

end Average

end MeasureTheory

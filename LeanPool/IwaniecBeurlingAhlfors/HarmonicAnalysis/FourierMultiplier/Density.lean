/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Density of the Schwartz functions with Fourier transform supported off the origin

`V` is a finite-dimensional real inner product space with its Lebesgue measure, of dimension
`d > 0`. `HarmonicAnalysis.exists_tendsto_hasCompactFourierSupportOffZero` is Proposition 2.4.23
(ii) of Hytönen–van Neerven–Veraar–Weis (HNVW), for Schwartz functions: for every Schwartz function
`f` there are Schwartz functions `f_j` with Fourier transforms in `C_c^∞ (V ∖ {0})` such that
`f_j → f` in `L^p` for every `1 < p < ∞`, and `𝓕 f_j → 𝓕 f` in `L^1`.

## Main results

* `HarmonicAnalysis.lintegral_rpow_lintegral_mul_le`: Hölder's inequality for the measure `w dν`
  and Tonelli's theorem, the computation of Young's inequality (HNVW, Lemma 1.2.30);
  `HarmonicAnalysis.lintegral_rpow_lintegral_le`: Minkowski's integral inequality.
* `HarmonicAnalysis.mollify ϕ f t`, the mollification `ϕ_t ∗ f` with `ϕ_t (x) = t^{−d} ϕ (x / t)`:
  `𝓕 (ϕ_t ∗ f) = 𝓕 ϕ (t ·) 𝓕 f` (`HarmonicAnalysis.fourier_mollify`),
  `(ϕ_t ∗ f) (x) = ∫ ϕ (y) f (x − t y) dy` (`HarmonicAnalysis.mollify_apply`).
* `HarmonicAnalysis.tendsto_eLpNorm_mollify_sub` (HNVW, Proposition 1.2.32): if `∫ ϕ = 1`, then
  `ϕ_t ∗ f → f` in `L^p`, `1 ≤ p < ∞`, as `t → 0`;
  `HarmonicAnalysis.tendsto_eLpNorm_mollify_atTop`: `ϕ_R ∗ f → 0` in `L^p`, `1 < p < ∞`, as
  `R → ∞`; and, on the Fourier side, `HarmonicAnalysis.tendsto_eLpNorm_fourier_mollify_sub` and
  `HarmonicAnalysis.tendsto_eLpNorm_fourier_mollify_atTop`.
* `HarmonicAnalysis.HasCompactFourierSupportOffZero`: the Fourier transform is compactly supported
  in `V ∖ {0}`; `HarmonicAnalysis.exists_tendsto_hasCompactFourierSupportOffZero`: the density.

## Proof

That of HNVW, p. 118: `f_j = (ϕ_{δ_j} − ϕ_{R_j}) ∗ f`, where `δ_j ↓ 0`, `R_j → ∞` and `𝓕 ϕ` is a
bump function equal to `1` near `0`, so that `𝓕 f_j = (𝓕 ϕ (δ_j ·) − 𝓕 ϕ (R_j ·)) 𝓕 f`. The
preliminary truncation `φ (ε ·) f` of HNVW, which makes the Fourier transform smooth, is not needed
for a Schwartz function. HNVW states the limits without proof. `ϕ_t ∗ f → f` in `L^p` is their
Proposition 1.2.32, proved here as there: Minkowski's integral inequality, the continuity of the
translations in `L^p` (in Mathlib) and dominated convergence. `‖ϕ_R ∗ f‖_p → 0` is Young's
inequality `‖ϕ_R ∗ f‖_p ≤ ‖ϕ_R‖_p ‖f‖_1` with `‖ϕ_R‖_p = R^{−d (1 − 1/p)} ‖ϕ‖_p`. The limits on the
Fourier side are by dominated convergence.

## A correction to the source

HNVW's Proposition 2.4.23 is about the space `L^p ∩ L_Fourier^1`, `L_Fourier^1` the inverse
Fourier transforms of
`L^1`, and its part (i) lists `C_c^∞ (ℝ^d ∖ {0})` among the dense subspaces. That space is dense in
`L^p` but not in `L^p ∩ L_Fourier^1`: its functions vanish at `0`, and `|f (0)| ≤ ‖𝓕 f‖_1`. The
proof there
does not treat it. Part (ii), used here, is not affected.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I*, Ergebnisse
  der Mathematik 63, Springer, 2016: Lemma 1.2.30 and Proposition 1.2.32 (pp. 28–29), Lemma 2.4.8
  (p. 109), Proposition 2.4.23 (p. 118).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform ENNReal ContDiff

namespace HarmonicAnalysis

/-- The `p`-th power of the `L^p` norm is the integral of the `p`-th power of the norm,
`0 < p < ∞`. -/
theorem eLpNorm_ofReal_rpow_eq_lintegral {S F : Type*} [NormedAddCommGroup F]
    {mS : MeasurableSpace S} {ν : Measure S} {p : ℝ} (hp : 0 < p) {f : S → F}
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm f (ENNReal.ofReal p) ν ^ p = ∫⁻ z, ‖f z‖ₑ ^ p ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-! ### Young's inequality -/

/-- The computation in the proof of Young's inequality (HNVW, Lemma 1.2.30): for `1 ≤ p`,
`∫ (∫ w (y) h (x, y) dy)^p dx ≤ (∫ w)^{p − 1} ∫ w (y) ∫ h (x, y)^p dx dy`, by Hölder's inequality
for the measure `w dν` and Tonelli's theorem. -/
theorem lintegral_rpow_lintegral_mul_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {w : β → ℝ≥0∞} (hw : Measurable w)
    {h : α → β → ℝ≥0∞} (hh : Measurable (Function.uncurry h)) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, (∫⁻ y, w y * h x y ∂ν) ^ p ∂μ ≤
      (∫⁻ y, w y ∂ν) ^ (p - 1) * ∫⁻ y, w y * ∫⁻ x, h x y ^ p ∂μ ∂ν := by
  have hp0 : 0 < p := by linarith
  have hmeas : Measurable (Function.uncurry fun x y => w y * h x y ^ p) :=
    (hw.comp measurable_snd).mul (hh.pow_const p)
  have key : ∀ x, (∫⁻ y, w y * h x y ∂ν) ^ p ≤
      (∫⁻ y, w y ∂ν) ^ (p - 1) * ∫⁻ y, w y * h x y ^ p ∂ν := by
    intro x
    have hhx : Measurable (h x) := hh.comp measurable_prodMk_left
    rcases hp.eq_or_lt with rfl | hp1
    · simp
    have hpq : p.HolderConjugate (p / (p - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent hp1).2 rfl
    set q := p / (p - 1)
    have hq0 : 0 < q := hpq.symm.pos
    have h1 : ∀ y, w y * h x y = ((fun y => w y ^ (1 / q)) * fun y => w y ^ (1 / p) * h x y) y := by
      intro y
      rw [Pi.mul_apply, ← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity)
        (by positivity), add_comm, hpq.one_div_add_one_div, div_one, ENNReal.rpow_one]
    have h2 : ∀ y, (w y ^ (1 / p) * h x y) ^ p = w y * h x y ^ p := fun y => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
        ENNReal.rpow_one]
    have h3 : ∀ y, (w y ^ (1 / q)) ^ q = w y := fun y => by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq.symm
      (f := fun y => w y ^ (1 / q)) (g := fun y => w y ^ (1 / p) * h x y)
      (hw.pow_const _).aemeasurable ((hw.pow_const _).mul hhx).aemeasurable
    simp only [← h1, h2, h3] at hH
    calc (∫⁻ y, w y * h x y ∂ν) ^ p
        ≤ ((∫⁻ y, w y ∂ν) ^ (1 / q) * (∫⁻ y, w y * h x y ^ p ∂ν) ^ (1 / p)) ^ p := by
          gcongr
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
          congr 2
          simp only [q]
          field_simp
  calc ∫⁻ x, (∫⁻ y, w y * h x y ∂ν) ^ p ∂μ
      ≤ ∫⁻ x, (∫⁻ y, w y ∂ν) ^ (p - 1) * ∫⁻ y, w y * h x y ^ p ∂ν ∂μ := lintegral_mono key
    _ = (∫⁻ y, w y ∂ν) ^ (p - 1) * ∫⁻ x, ∫⁻ y, w y * h x y ^ p ∂ν ∂μ :=
        lintegral_const_mul _ hmeas.lintegral_prod_right'
    _ = _ := by
        rw [lintegral_lintegral_swap hmeas.aemeasurable]
        congr 1
        refine lintegral_congr fun y => ?_
        exact lintegral_const_mul _ ((hh.comp measurable_prodMk_right).pow_const p)

/-- Minkowski's integral inequality, in the form of Young's inequality:
`‖∫ w (s) F (·, s) dν (s)‖_p ≤ ‖w‖_1 C` when `‖F (·, s)‖_p ≤ C` for almost every `s`. -/
theorem eLpNorm_integral_smul_le {X α β : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {p : ℝ} (hp : 1 ≤ p) {w : β → ℝ} (hw : Measurable w) {F : α → β → X}
    (hF : StronglyMeasurable (Function.uncurry F)) {C : ℝ≥0∞}
    (hC : ∀ᵐ s ∂ν, eLpNorm (fun x => F x s) (ENNReal.ofReal p) μ ≤ C) :
    eLpNorm (fun x => ∫ s, w s • F x s ∂ν) (ENNReal.ofReal p) μ ≤ (∫⁻ s, ‖w s‖ₑ ∂ν) * C := by
  have hp0 : 0 < p := by linarith
  have hwF : StronglyMeasurable fun x => ∫ s, w s • F x s ∂ν :=
    ((hw.comp measurable_snd).stronglyMeasurable.smul hF).integral_prod_right
  set A := ∫⁻ s, ‖w s‖ₑ ∂ν
  rw [← ENNReal.rpow_le_rpow_iff hp0, eLpNorm_ofReal_rpow_eq_lintegral hp0 hwF.aestronglyMeasurable]
  calc ∫⁻ x, ‖∫ s, w s • F x s ∂ν‖ₑ ^ p ∂μ
      ≤ ∫⁻ x, (∫⁻ s, ‖w s‖ₑ * ‖F x s‖ₑ ∂ν) ^ p ∂μ := by
        refine lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ hp0.le
        refine (eNorm_integral_le_lintegral_eNorm _).trans_eq ?_
        simp_rw [eNorm_smul]
    _ ≤ A ^ (p - 1) * ∫⁻ s, ‖w s‖ₑ * (∫⁻ x, ‖F x s‖ₑ ^ p ∂μ) ∂ν :=
        lintegral_rpow_lintegral_mul_le hw.eNorm hF.eNorm hp
    _ ≤ A ^ (p - 1) * ∫⁻ s, ‖w s‖ₑ * C ^ p ∂ν := by
        refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
        filter_upwards [hC] with s hs
        rw [← eLpNorm_ofReal_rpow_eq_lintegral hp0
          (hF.comp_measurable measurable_prodMk_right).aestronglyMeasurable (f := fun x => F x s)]
        gcongr
    _ = (A * C) ^ p := by
        rw [lintegral_mul_const _ hw.eNorm, ← mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        congr 1
        conv_lhs => rw [show ∫⁻ s, ‖w s‖ₑ ∂ν = A ^ (1 : ℝ) from (ENNReal.rpow_one A).symm]
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, sub_add_cancel]

/-- Minkowski's integral inequality, for `1 ≤ p` and a finite left side:
`(∫ (∫ h (x, y) dy)^p dx)^{1/p} ≤ ∫ (∫ h (x, y)^p dx)^{1/p} dy`. With `F (x) = ∫ h (x, y) dy`, by
Tonelli's theorem and Hölder's inequality, `∫ F^p = ∫ ∫ h (x, y) F (x)^{p − 1} dx dy` is at most the
right side times `(∫ F^p)^{1 − 1/p}`. -/
theorem lintegral_rpow_lintegral_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {h : α → β → ℝ≥0∞}
    (hh : Measurable (Function.uncurry h)) {p : ℝ} (hp : 1 ≤ p)
    (hI : ∫⁻ x, (∫⁻ y, h x y ∂ν) ^ p ∂μ ≠ ⊤) :
    (∫⁻ x, (∫⁻ y, h x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ y, (∫⁻ x, h x y ^ p ∂μ) ^ (1 / p) ∂ν := by
  rcases hp.eq_or_lt with rfl | hp1
  · simp only [ENNReal.rpow_one, div_one]
    rw [lintegral_lintegral_swap hh.aemeasurable]
  have hp0 : 0 < p := by linarith
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).2 rfl
  set q := p / (p - 1)
  set F : α → ℝ≥0∞ := fun x => ∫⁻ y, h x y ∂ν
  have hF : Measurable F := hh.lintegral_prod_right'
  set I := ∫⁻ x, F x ^ p ∂μ
  set S := ∫⁻ y, (∫⁻ x, h x y ^ p ∂μ) ^ (1 / p) ∂ν
  have hy : ∀ y, Measurable fun x => h x y := fun y => hh.comp measurable_prodMk_right
  have hle : I ≤ S * I ^ (1 / q) := by
    calc I = ∫⁻ x, ∫⁻ y, h x y * F x ^ (p - 1) ∂ν ∂μ := by
          refine lintegral_congr fun x => ?_
          have hhx : Measurable (h x) := hh.comp measurable_prodMk_left
          rw [lintegral_mul_const _ hhx]
          conv_lhs => rw [show p = 1 + (p - 1) by ring,
            ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith), ENNReal.rpow_one]
      _ = ∫⁻ y, ∫⁻ x, h x y * F x ^ (p - 1) ∂μ ∂ν :=
          lintegral_lintegral_swap
            (hh.mul ((hF.comp measurable_fst).pow_const (p - 1))).aemeasurable
      _ ≤ ∫⁻ y, (∫⁻ x, h x y ^ p ∂μ) ^ (1 / p) * I ^ (1 / q) ∂ν := by
          refine lintegral_mono fun y => ?_
          have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (f := fun x => h x y)
            (g := fun x => F x ^ (p - 1)) (hy y).aemeasurable (hF.pow_const _).aemeasurable
          have hFq : ∀ x, (F x ^ (p - 1)) ^ q = F x ^ p := fun x => by
            rw [← ENNReal.rpow_mul, hpq.sub_one_mul_conj]
          simpa only [Pi.mul_apply, hFq] using hH
      _ = S * I ^ (1 / q) :=
          lintegral_mul_const _ ((hh.pow_const p).lintegral_prod_left'.pow_const _)
  rcases eq_or_ne I 0 with h0 | h0
  · rw [h0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  have hq0 : I ^ (1 / q) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 h0) hI).ne'
  have hqt : I ^ (1 / q) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hpq.symm.one_div_nonneg hI
  rw [← ENNReal.mul_le_mul_iff_left hq0 hqt, ← ENNReal.rpow_add _ _ h0 hI,
    hpq.one_div_add_one_div, div_one, ENNReal.rpow_one]
  exact hle

/-! ### Mollification -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The mollification `ϕ_t ∗ f` of a Schwartz function `f`, where `ϕ_t (x) = t^{−d} ϕ (x / t)` for
`t > 0`, `d = dim V`, defined by its Fourier transform `𝓕 ϕ (t ·) 𝓕 f`; for `t = 0` it is
`f ∫ ϕ`. -/
def mollify (ϕ f : 𝓢(V, ℂ)) (t : ℝ) : 𝓢(V, ℂ) :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (fun ξ => 𝓕 ϕ (t • ξ)) (𝓕 f))

/-- `𝓕 (ϕ_t ∗ f) = 𝓕 ϕ (t ·) 𝓕 f`. -/
theorem fourier_mollify (ϕ f : 𝓢(V, ℂ)) (t : ℝ) (ξ : V) :
    𝓕 (mollify ϕ f t) ξ = 𝓕 ϕ (t • ξ) * 𝓕 f ξ := by
  have hg : (fun ξ => 𝓕 ϕ (t • ξ)).HasTemperateGrowth :=
    (𝓕 ϕ).hasTemperateGrowth.comp (by fun_prop : (fun ξ : V => t • ξ).HasTemperateGrowth)
  rw [mollify, FourierTransform.fourier_fourierInv_eq, SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul]

/-- `(ϕ_t ∗ f) (x) = ∫ ϕ (y) f (x − t y) dy` (HNVW, Lemma 2.4.8 and (1.4)): insert
`𝓕 ϕ (t ξ) = ∫ ϕ (y) e^{−2πi ⟨t ξ, y⟩} dy` in `∫ 𝓕 ϕ (t ξ) 𝓕 f (ξ) e^{2πi ⟨ξ, x⟩} dξ`, and use
Fubini's theorem and Fourier inversion for `f`. -/
theorem mollify_apply (ϕ f : 𝓢(V, ℂ)) (t : ℝ) (x : V) :
    mollify ϕ f t x = ∫ y, ϕ y * f (x - t • y) := by
  set L : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := t • innerₗ V
  have hL : Continuous fun p : V × V => L p.1 p.2 := by
    simp only [L, LinearMap.smul_apply, innerₗ_apply_apply]
    fun_prop
  set G : V → ℂ := fun ξ => 𝐞 (inner ℝ ξ x) • 𝓕 f ξ
  have hG : Integrable G := by
    refine (𝓕 f).integrable.mono ?_ (ae_of_all _ fun ξ => by simp [G])
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (𝓕 f).continuous).aestronglyMeasurable
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (L := L) Real.continuous_fourierChar hL ϕ.integrable hG
  have h1 : ∀ ξ, VectorFourier.fourierIntegral 𝐞 volume L ϕ ξ = 𝓕 ϕ (t • ξ) := fun ξ => by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simp [VectorFourier.fourierIntegral, L, real_inner_smul_right]
  have h2 : ∀ y, VectorFourier.fourierIntegral 𝐞 volume L.flip G y = f (x - t • y) := fun y => by
    have : f (x - t • y) = 𝓕⁻ (𝓕 f) (x - t • y) := by
      rw [FourierTransform.fourierInv_fourier_eq]
    rw [this, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [G, L, LinearMap.flip_apply, LinearMap.smul_apply, innerₗ_apply_apply, smul_smul,
      inner_sub_right, real_inner_smul_right, ← AddChar.map_add_eq_mul, smul_eq_mul]
    congr 2
    rw [real_inner_comm]
    ring
  simp only [h1, h2, smul_eq_mul] at h
  rw [← h, mollify, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  have hg : (fun ξ => 𝓕 ϕ (t • ξ)).HasTemperateGrowth :=
    (𝓕 ϕ).hasTemperateGrowth.comp (by fun_prop : (fun ξ : V => t • ξ).HasTemperateGrowth)
  simp only [SchwartzMap.smulLeftCLM_apply_apply hg, G, Circle.smul_def, smul_eq_mul]
  ring

/-- `‖g‖_p = (∫ |g|^p)^{1/p}` for continuous `g` and `0 < p < ∞`. -/
private theorem eLpNorm_eq_lintegral_rpow {g : V → ℂ} (hg : Continuous g) {p : ℝ} (hp : 0 < p) :
    eLpNorm g (ENNReal.ofReal p) volume = (∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    hg.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]

/-- `‖g_t‖_p → 0` if `‖g_t‖_p^p → 0`. -/
private theorem tendsto_eLpNorm_of_rpow {ι : Type*} {l : Filter ι} {g : ι → V → ℂ} {p : ℝ}
    (hp : 0 < p) (h : Tendsto (fun t => eLpNorm (g t) (ENNReal.ofReal p) volume ^ p) l (𝓝 0)) :
    Tendsto (fun t => eLpNorm (g t) (ENNReal.ofReal p) volume) l (𝓝 0) := by
  have := h.ennrpow_const (1 / p)
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at this
  refine this.congr fun t => ?_
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- Translations are continuous in `L^p`, `1 ≤ p < ∞`: `‖f (· − h) − f‖_p → 0` as `h → 0`. -/
theorem tendsto_eLpNorm_translate_sub (f : 𝓢(V, ℂ)) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun h : V => eLpNorm (fun x => f (x - h) - f x) (ENNReal.ofReal p) volume) (𝓝 0)
      (𝓝 0) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using hp⟩
  have hmp : ∀ h : V, MeasurePreserving (fun x : V => x - h) volume volume := fun h =>
    measurePreserving_sub_right volume h
  let g : C(V, C(V, V)) := ContinuousMap.curry ⟨fun z : V × V => z.2 - z.1, by fun_prop⟩
  have hf := f.memLp (ENNReal.ofReal p) volume
  have h : Tendsto (fun h => (hf.comp_measurePreserving (hmp h)).toLp _) (𝓝 0)
      (𝓝 ((hf.comp_measurePreserving (hmp 0)).toLp _)) :=
    Filter.Tendsto.compMeasurePreservingLp (l := 𝓝 (0 : V)) (g := fun h => g h)
      (g₀ := g 0) (tendsto_const_nhds (x := hf.toLp f)) (g.continuous.tendsto 0)
      (fun h => hmp h) (hmp 0) ENNReal.ofReal_ne_top
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm''] at h
  refine h.congr fun h => ?_
  congr 1
  funext x
  simp

/-- Mollifiers (HNVW, Proposition 1.2.32, for Schwartz functions): if `∫ ϕ = 1`, then
`‖ϕ_t ∗ f − f‖_p → 0` as `t → 0`, for `1 ≤ p < ∞`. By
`(ϕ_t ∗ f) (x) − f (x) = ∫ ϕ (y) (f (x − t y) − f (x)) dy` and Minkowski's integral inequality,
`‖ϕ_t ∗ f − f‖_p ≤ ∫ |ϕ (y)| ‖f (· − t y) − f‖_p dy`, which tends to `0` by the continuity of the
translations in `L^p` and dominated convergence, `‖f (· − t y) − f‖_p ≤ 2 ‖f‖_p`. -/
theorem tendsto_eLpNorm_mollify_sub {ϕ : 𝓢(V, ℂ)} (hϕ : ∫ y, ϕ y = 1) (f : 𝓢(V, ℂ)) {p : ℝ}
    (hp : 1 ≤ p) :
    Tendsto (fun t => eLpNorm (fun x => mollify ϕ f t x - f x) (ENNReal.ofReal p) volume) (𝓝 0)
      (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hP : 1 ≤ ENNReal.ofReal p := by simpa using hp
  have hϕ1 : ∫⁻ y, ‖ϕ y‖ₑ ≠ ⊤ := ϕ.integrable.2.ne
  set N : V → ℝ≥0∞ := fun h => eLpNorm (fun x => f (x - h) - f x) (ENNReal.ofReal p) volume
  set M : ℝ≥0∞ := 2 * eLpNorm f (ENNReal.ofReal p) volume
  have hM : M ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top (f.memLp _).eLpNorm_lt_top.ne
  have hNM : ∀ h, N h ≤ M := by
    intro h
    refine (eLpNorm_sub_le hP (f := fun x => f (x - h)) (g := f)).trans_eq ?_
    have h1 := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p)
      f.continuous.aestronglyMeasurable (measurePreserving_sub_right (volume : Measure V) h)
    simp only [M, two_mul]
    exact congrArg (· + _) h1
  -- The integrand `h (x, y) = |ϕ (y)| |f (x − t y) − f (x)|`.
  have hmeas : ∀ t : ℝ, Measurable (Function.uncurry fun x y : V =>
      ‖ϕ y‖ₑ * ‖f (x - t • y) - f x‖ₑ) := fun t =>
    (by fun_prop : Continuous fun z : V × V => ‖ϕ z.2‖ₑ).measurable.mul
      (by fun_prop : Continuous fun z : V × V => ‖f (z.1 - t • z.2) - f z.1‖ₑ).measurable
  have hnorm : ∀ (t : ℝ) (y : V), (∫⁻ x, (‖ϕ y‖ₑ * ‖f (x - t • y) - f x‖ₑ) ^ p) ^ (1 / p) =
      ‖ϕ y‖ₑ * N (t • y) := by
    intro t y
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    rw [lintegral_const_mul _ ((by fun_prop : Continuous fun x =>
      ‖f (x - t • y) - f x‖ₑ).measurable.pow_const p),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one,
      ← eLpNorm_eq_lintegral_rpow (g := fun x => f (x - t • y) - f x) (by fun_prop) hp0]
  have hle : ∀ t : ℝ, eLpNorm (fun x => mollify ϕ f t x - f x) (ENNReal.ofReal p) volume ≤
      ∫⁻ y, ‖ϕ y‖ₑ * N (t • y) := by
    intro t
    -- Finiteness, by Young's computation.
    have hI : ∫⁻ x, (∫⁻ y, ‖ϕ y‖ₑ * ‖f (x - t • y) - f x‖ₑ) ^ p ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_rpow_lintegral_mul_le (w := fun y => ‖ϕ y‖ₑ)
        (h := fun x y => ‖f (x - t • y) - f x‖ₑ) ϕ.continuous.eNorm.measurable
        (by fun_prop : Continuous fun z : V × V => ‖f (z.1 - t • z.2) - f z.1‖ₑ).measurable hp)
      refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hϕ1)
        (ne_top_of_le_ne_top (b := (∫⁻ y, ‖ϕ y‖ₑ) * M ^ p) (ENNReal.mul_ne_top hϕ1
          (ENNReal.rpow_ne_top_of_nonneg hp0.le hM)) ?_)
      rw [← lintegral_mul_const _ ϕ.continuous.eNorm.measurable]
      gcongr with y
      rw [← eLpNorm_ofReal_rpow_eq_lintegral hp0 (f := fun x => f (x - t • y) - f x)
        (by fun_prop : Continuous fun x => f (x - t • y) - f x).aestronglyMeasurable]
      exact ENNReal.rpow_le_rpow (hNM _) hp0.le
    have hmin := lintegral_rpow_lintegral_le (hmeas t) hp hI
    simp_rw [hnorm] at hmin
    refine le_trans ?_ hmin
    rw [eLpNorm_eq_lintegral_rpow (by fun_prop) hp0]
    refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ hp0.le)
      (by positivity)
    have hi : Integrable fun y => ϕ y * f (x - t • y) := by
      refine (ϕ.integrable.mul_const (SchwartzMap.seminorm ℝ 0 0 f : ℂ)).mono
        (by fun_prop : Continuous fun y => ϕ y * f (x - t • y)).aestronglyMeasurable
        (ae_of_all _ fun y => ?_)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (f.norm_le_seminorm ℝ _) (norm_nonneg _)
    have hsub : mollify ϕ f t x - f x = ∫ y, ϕ y * (f (x - t • y) - f x) := by
      simp_rw [mul_sub]
      rw [integral_sub hi (ϕ.integrable.mul_const _), integral_mul_const, hϕ, one_mul,
        mollify_apply]
    rw [hsub]
    refine (eNorm_integral_le_lintegral_eNorm _).trans_eq ?_
    simp_rw [eNorm_mul]
  -- Dominated convergence.
  have hlim : Tendsto (fun t : ℝ => ∫⁻ y, ‖ϕ y‖ₑ * N (t • y)) (𝓝 0) (𝓝 0) := by
    have h0 : ∫⁻ _ : V, (0 : ℝ≥0∞) = 0 := lintegral_zero
    rw [← h0]
    refine tendsto_lintegral_filter_of_dominated_convergence (fun y => ‖ϕ y‖ₑ * M)
      (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ae_of_all _ fun y => ?_) ?_
      (ae_of_all _ fun y => ?_)
    · simp_rw [← hnorm]
      exact ((hmeas t).pow_const p).lintegral_prod_left'.pow_const _
    · gcongr
      exact hNM _
    · rw [lintegral_mul_const _ ϕ.continuous.eNorm.measurable]
      exact ENNReal.mul_ne_top hϕ1 hM
    · have h1 : Tendsto (fun t : ℝ => t • y) (𝓝 0) (𝓝 0) := by
        have : Tendsto (fun t : ℝ => t • y) (𝓝 0) (𝓝 ((0 : ℝ) • y)) :=
          (by fun_prop : Continuous fun t : ℝ => t • y).tendsto 0
        rwa [zero_smul] at this
      have := ENNReal.Tendsto.const_mul ((tendsto_eLpNorm_translate_sub f hp).comp h1)
        (a := ‖ϕ y‖ₑ) (Or.inr eNorm_ne_top)
      rwa [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hle

/-- The change of variables `w = R y`: `∫ F (R y) dy = R^{−d} ∫ F`, `R > 0`. -/
private theorem lintegral_comp_smul {F : V → ℝ≥0∞} (hF : Measurable F) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y, F (R • y) = ENNReal.ofReal (R ^ Module.finrank ℝ V)⁻¹ * ∫⁻ y, F y := by
  rw [← lintegral_map hF (measurable_const_smul R), Measure.map_addHaar_smul volume hR.ne',
    lintegral_smul_measure, smul_eq_mul, abs_of_pos (by positivity)]

/-- For `1 < p < ∞` and `d > 0`, `‖ϕ_R ∗ f‖_p → 0` as `R → ∞`: by Young's inequality
`‖ϕ_R ∗ f‖_p ≤ ‖ϕ_R‖_p ‖f‖_1`, and `‖ϕ_R‖_p = R^{−d (1 − 1/p)} ‖ϕ‖_p`. -/
theorem tendsto_eLpNorm_mollify_atTop [Nontrivial V] (ϕ f : 𝓢(V, ℂ)) {p : ℝ} (hp : 1 < p) :
    Tendsto (fun R => eLpNorm (mollify ϕ f R) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  set d := Module.finrank ℝ V
  have hd : 0 < d := Module.finrank_pos
  have hf1 : ∫⁻ y, ‖f y‖ₑ ≠ ⊤ := f.integrable.2.ne
  have hϕp : ∫⁻ x, ‖ϕ x‖ₑ ^ p ≠ ⊤ := by
    rw [← eLpNorm_ofReal_rpow_eq_lintegral hp0 ϕ.continuous.aestronglyMeasurable]
    exact ENNReal.rpow_ne_top_of_nonneg hp0.le (ϕ.memLp _).eLpNorm_lt_top.ne
  set A : ℝ≥0∞ := (∫⁻ y, ‖f y‖ₑ) ^ (p - 1) * ((∫⁻ y, ‖f y‖ₑ) * ∫⁻ x, ‖ϕ x‖ₑ ^ p)
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hf1)
    (ENNReal.mul_ne_top hf1 hϕp)
  have hle : ∀ R : ℝ, 0 < R → eLpNorm (mollify ϕ f R) (ENNReal.ofReal p) volume ^ p ≤
      ENNReal.ofReal ((R ^ d)⁻¹ ^ (p - 1)) * A := by
    intro R hR
    set c : ℝ≥0∞ := ENNReal.ofReal (R ^ d)⁻¹
    -- `(ϕ_R ∗ f) (x) = ∫ f (z) ϕ_R (x − z) dz`
    have h1 : ∀ x, ‖mollify ϕ f R x‖ₑ ≤ ∫⁻ z, ‖f z‖ₑ * (c * ‖ϕ (R⁻¹ • (x - z))‖ₑ) := by
      intro x
      rw [mollify_apply]
      refine (eNorm_integral_le_lintegral_eNorm _).trans_eq ?_
      have h2 : ∀ y, ‖ϕ y * f (x - R • y)‖ₑ =
          (fun w => ‖ϕ (R⁻¹ • w)‖ₑ * ‖f (x - w)‖ₑ) (R • y) := fun y => by
        simp only [smul_smul, inv_mul_cancel₀ hR.ne', one_smul, eNorm_mul]
      have hm : Measurable fun w => ‖ϕ (R⁻¹ • w)‖ₑ * ‖f (x - w)‖ₑ :=
        (by fun_prop : Continuous fun w => ‖ϕ (R⁻¹ • w)‖ₑ).measurable.mul
          (by fun_prop : Continuous fun w => ‖f (x - w)‖ₑ).measurable
      simp_rw [h2]
      rw [lintegral_comp_smul hm hR, ← lintegral_const_mul _ hm,
        ← lintegral_sub_left_eq_self _ x]
      refine lintegral_congr fun z => ?_
      simp only [sub_sub_cancel, c, d]
      ring
    rw [eLpNorm_ofReal_rpow_eq_lintegral hp0 (mollify ϕ f R).continuous.aestronglyMeasurable]
    refine (lintegral_mono fun x => ENNReal.rpow_le_rpow (h1 x) hp0.le).trans
      ((lintegral_rpow_lintegral_mul_le (w := fun z => ‖f z‖ₑ)
        (h := fun x z => c * ‖ϕ (R⁻¹ • (x - z))‖ₑ) f.continuous.eNorm.measurable ?_ hp.le).trans_eq
        ?_)
    · exact measurable_const.mul
        (by fun_prop : Continuous fun z : V × V => ‖ϕ (R⁻¹ • (z.1 - z.2))‖ₑ).measurable
    · have h3 : ∀ z, ∫⁻ x, (c * ‖ϕ (R⁻¹ • (x - z))‖ₑ) ^ p =
          ENNReal.ofReal ((R ^ d)⁻¹ ^ (p - 1)) * ∫⁻ x, ‖ϕ x‖ₑ ^ p := by
        intro z
        rw [lintegral_sub_right_eq_self (fun x => (c * ‖ϕ (R⁻¹ • x)‖ₑ) ^ p) z]
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        rw [lintegral_const_mul _
          ((by fun_prop : Continuous fun x => ‖ϕ (R⁻¹ • x)‖ₑ).measurable.pow_const p),
          lintegral_comp_smul (F := fun x => ‖ϕ x‖ₑ ^ p) (ϕ.continuous.eNorm.measurable.pow_const p)
            (inv_pos.2 hR), ← mul_assoc]
        congr 1
        simp only [c]
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.rpow_sub_one (by positivity), inv_pow, inv_inv]
        field_simp
        rfl
      simp_rw [h3]
      rw [lintegral_mul_const _ f.continuous.eNorm.measurable]
      simp only [A]
      ring
  refine tendsto_eLpNorm_of_rpow hp0 (tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds ?_ (Eventually.of_forall fun _ => zero_le)
    ((eventually_gt_atTop 0).mono hle))
  have h4 : Tendsto (fun R : ℝ => (R ^ d)⁻¹ ^ (p - 1)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop hd.ne').inv_tendsto_atTop (𝕜 := ℝ)).rpow_const
      (p := p - 1) (Or.inr (by linarith))
    rwa [Real.zero_rpow (by linarith)] at this
  have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h4) (b := A) (Or.inr hA)
  rwa [ENNReal.ofReal_zero, zero_mul] at this

/-- On the Fourier side: if `∫ ϕ = 1`, then `‖𝓕 (ϕ_t ∗ f) − 𝓕 f‖_1 = ‖𝓕 ϕ (t ·) 𝓕 f − 𝓕 f‖_1 → 0`
as `t → 0`, by dominated convergence. -/
theorem tendsto_eLpNorm_fourier_mollify_sub {ϕ : 𝓢(V, ℂ)} (hϕ : ∫ y, ϕ y = 1) (f : 𝓢(V, ℂ)) :
    Tendsto (fun t => eLpNorm (fun ξ => 𝓕 (mollify ϕ f t) ξ - 𝓕 f ξ) 1 volume) (𝓝 0) (𝓝 0) := by
  set K := SchwartzMap.seminorm ℝ 0 0 (𝓕 ϕ)
  have hK : ∀ ξ, ‖𝓕 ϕ ξ - 1‖ₑ ≤ ENNReal.ofReal (K + 1) := fun ξ => by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans ?_)
    rw [norm_one]
    gcongr
    exact (𝓕 ϕ).norm_le_seminorm ℝ ξ
  have hϕ0 : 𝓕 ϕ 0 = 1 := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simpa using hϕ
  have heq : ∀ t, eLpNorm (fun ξ => 𝓕 (mollify ϕ f t) ξ - 𝓕 f ξ) 1 volume =
      ∫⁻ ξ, ‖𝓕 ϕ (t • ξ) - 1‖ₑ * ‖𝓕 f ξ‖ₑ := fun t => by
    rw [eLpNorm_one_eq_lintegral_eNorm (by fun_prop : Continuous fun ξ =>
      𝓕 (mollify ϕ f t) ξ - 𝓕 f ξ).aestronglyMeasurable]
    refine lintegral_congr fun ξ => ?_
    rw [fourier_mollify, ← eNorm_mul, sub_mul, one_mul]
  simp_rw [heq]
  have h0 : ∫⁻ _ : V, (0 : ℝ≥0∞) = 0 := lintegral_zero
  rw [← h0]
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun ξ => ENNReal.ofReal (K + 1) * ‖𝓕 f ξ‖ₑ)
    (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ae_of_all _ fun ξ => ?_) ?_
    (ae_of_all _ fun ξ => ?_)
  · exact (by fun_prop : Continuous fun ξ => ‖𝓕 ϕ (t • ξ) - 1‖ₑ).measurable.mul
      (𝓕 f).continuous.eNorm.measurable
  · gcongr
    exact hK _
  · rw [lintegral_const_mul _ (𝓕 f).continuous.eNorm.measurable]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (𝓕 f).integrable.2.ne
  · have h1 : Tendsto (fun t : ℝ => ‖𝓕 ϕ (t • ξ) - 1‖ₑ) (𝓝 0) (𝓝 0) := by
      have := (by fun_prop : Continuous fun t : ℝ => ‖𝓕 ϕ (t • ξ) - 1‖ₑ).tendsto 0
      simpa [hϕ0] using this
    have := ENNReal.Tendsto.mul_const h1 (b := ‖𝓕 f ξ‖ₑ) (Or.inr eNorm_ne_top)
    rwa [zero_mul] at this

/-- On the Fourier side: for `d > 0`, `‖𝓕 (ϕ_R ∗ f)‖_1 = ‖𝓕 ϕ (R ·) 𝓕 f‖_1 → 0` as `R → ∞`, by
dominated convergence. -/
theorem tendsto_eLpNorm_fourier_mollify_atTop [Nontrivial V] (ϕ f : 𝓢(V, ℂ)) :
    Tendsto (fun R => eLpNorm (𝓕 (mollify ϕ f R : V → ℂ)) 1 volume) atTop (𝓝 0) := by
  set K := SchwartzMap.seminorm ℝ 0 0 (𝓕 ϕ)
  have hK : ∀ ξ, ‖𝓕 ϕ ξ‖ₑ ≤ ENNReal.ofReal K := fun ξ => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((𝓕 ϕ).norm_le_seminorm ℝ ξ)
  have heq : ∀ R, eLpNorm (𝓕 (mollify ϕ f R : V → ℂ)) 1 volume =
      ∫⁻ ξ, ‖𝓕 ϕ (R • ξ)‖ₑ * ‖𝓕 f ξ‖ₑ := fun R => by
    rw [← SchwartzMap.fourier_coe,
      eLpNorm_one_eq_lintegral_eNorm (𝓕 (mollify ϕ f R)).continuous.aestronglyMeasurable]
    refine lintegral_congr fun ξ => ?_
    rw [fourier_mollify, eNorm_mul]
  simp_rw [heq]
  have h0 : ∫⁻ _ : V, (0 : ℝ≥0∞) = 0 := lintegral_zero
  rw [← h0]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun ξ => ENNReal.ofReal K * ‖𝓕 f ξ‖ₑ)
    (Eventually.of_forall fun R => ?_) (Eventually.of_forall fun R => ae_of_all _ fun ξ => ?_) ?_ ?_
  · exact (by fun_prop : Continuous fun ξ => ‖𝓕 ϕ (R • ξ)‖ₑ).measurable.mul
      (𝓕 f).continuous.eNorm.measurable
  · gcongr
    exact hK _
  · rw [lintegral_const_mul _ (𝓕 f).continuous.eNorm.measurable]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (𝓕 f).integrable.2.ne
  · filter_upwards [Measure.ae_ne volume 0] with ξ hξ
    have h1 : Tendsto (fun R : ℝ => R • ξ) atTop (cocompact V) := by
      rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      simp_rw [norm_smul]
      exact tendsto_norm_atTop_atTop.atTop_mul_const (norm_pos_iff.2 hξ)
    have h2 : Tendsto (fun R : ℝ => ‖𝓕 ϕ (R • ξ)‖ₑ) atTop (𝓝 0) := by
      have := ((𝓕 ϕ).tendsto_cocompact.comp h1).eNorm
      rwa [eNorm_zero] at this
    have := ENNReal.Tendsto.mul_const h2 (b := ‖𝓕 f ξ‖ₑ) (Or.inr eNorm_ne_top)
    rwa [zero_mul] at this

/-! ### Density -/

/-- The Schwartz functions whose Fourier transform is compactly supported in `V ∖ {0}`, that is, the
inverse Fourier transforms of the functions of `C_c^∞ (V ∖ {0})`. -/
def HasCompactFourierSupportOffZero (f : 𝓢(V, ℂ)) : Prop :=
  HasCompactSupport (𝓕 (f : V → ℂ)) ∧ 0 ∉ tsupport (𝓕 (f : V → ℂ))

/-- **HNVW, Proposition 2.4.23 (ii)**, for a Schwartz function `f` (and `d > 0`): there are Schwartz
functions `f_j` with Fourier transforms compactly supported in `V ∖ {0}` such that `f_j → f` in
`L^p` for every `1 < p < ∞`, and `𝓕 f_j → 𝓕 f` in `L^1`. They are
`f_j = (ϕ_{δ_j} − ϕ_{R_j}) ∗ f`, where `𝓕 ϕ` is a bump function equal to `1` near `0`. -/
theorem exists_tendsto_hasCompactFourierSupportOffZero [Nontrivial V] (f : 𝓢(V, ℂ)) :
    ∃ φ : ℕ → 𝓢(V, ℂ), (∀ j, HasCompactFourierSupportOffZero (φ j)) ∧
      (∀ p : ℝ, 1 < p → Tendsto (fun j => eLpNorm (fun x => φ j x - f x) (ENNReal.ofReal p) volume)
        atTop (𝓝 0)) ∧
      Tendsto (fun j => eLpNorm (fun ξ => 𝓕 (φ j) ξ - 𝓕 f ξ) 1 volume) atTop (𝓝 0) := by
  -- `ϕ` with `𝓕 ϕ = χ`, a bump function equal to `1` on the unit ball
  let χ : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have hχc : HasCompactSupport fun ξ => (χ ξ : ℂ) :=
    χ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hχs : ContDiff ℝ ∞ fun ξ => (χ ξ : ℂ) := Complex.ofRealCLM.contDiff.comp χ.contDiff
  let X : 𝓢(V, ℂ) := hχc.toSchwartzMap hχs
  have hX : ∀ ξ, X ξ = χ ξ := fun _ => rfl
  set ϕ : 𝓢(V, ℂ) := 𝓕⁻ X
  have hϕX : 𝓕 ϕ = X := FourierTransform.fourier_fourierInv_eq X
  have hϕ : ∫ y, ϕ y = 1 := by
    have h : 𝓕 ϕ 0 = 1 := by
      rw [hϕX, hX, χ.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one),
        Complex.ofReal_one]
    rw [SchwartzMap.fourier_coe, Real.fourier_eq] at h
    simpa using h
  -- `f_j = (ϕ_{δ_j} − ϕ_{R_j}) ∗ f` with `δ_j = 1 / (j + 1)`, `R_j = j + 1`
  set φ : ℕ → 𝓢(V, ℂ) := fun j =>
    mollify ϕ f (1 / ((j : ℝ) + 1)) - mollify ϕ f ((j : ℝ) + 1)
  have hδ : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hR : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hφ : ∀ j ξ, 𝓕 (φ j) ξ =
      (χ ((1 / ((j : ℝ) + 1)) • ξ) - χ (((j : ℝ) + 1) • ξ)) * 𝓕 f ξ := fun j ξ => by
    have h : 𝓕 (φ j) = 𝓕 (mollify ϕ f (1 / ((j : ℝ) + 1))) - 𝓕 (mollify ϕ f ((j : ℝ) + 1)) :=
      map_sub (FourierTransform.fourierCLM ℂ 𝓢(V, ℂ)) _ _
    rw [h, sub_apply, fourier_mollify, fourier_mollify, hϕX, hX, hX, sub_mul]
  refine ⟨φ, fun j => ⟨?_, ?_⟩, fun p hp => ?_, ?_⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : V) (2 * ((j : ℝ) + 1))) fun ξ hξ => ?_
    by_contra h
    rw [mem_closedBall_zero_iff, not_le] at h
    have hj : (0 : ℝ) < j + 1 := by positivity
    have h1 : χ ((1 / ((j : ℝ) + 1)) • ξ) = 0 := by
      refine χ.zero_of_le_dist ?_
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity), one_div,
        ← div_eq_inv_mul, le_div_iff₀ hj]
      exact h.le
    have h2 : χ (((j : ℝ) + 1) • ξ) = 0 := by
      refine χ.zero_of_le_dist ?_
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hj.le]
      change 2 ≤ _
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), norm_nonneg ξ]
    refine hξ ?_
    rw [← SchwartzMap.fourier_coe, hφ, h1, h2]
    simp
  · rw [notMem_tsupport_iff_eventuallyEq]
    have hj : (0 : ℝ) < j + 1 := by positivity
    filter_upwards [Metric.closedBall_mem_nhds (0 : V) (one_div_pos.2 hj)] with ξ hξ
    rw [mem_closedBall_zero_iff, le_div_iff₀ hj] at hξ
    have h1 : χ ((1 / ((j : ℝ) + 1)) • ξ) = 1 := by
      refine χ.one_of_mem_closedBall ?_
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (by positivity), one_div,
        ← div_eq_inv_mul, div_le_iff₀ hj]
      change ‖ξ‖ ≤ 1 * _
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), norm_nonneg ξ]
    have h2 : χ (((j : ℝ) + 1) • ξ) = 1 := by
      refine χ.one_of_mem_closedBall ?_
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hj.le, mul_comm]
      exact hξ
    rw [← SchwartzMap.fourier_coe, hφ, h1, h2]
    simp
  · have hP : 1 ≤ ENNReal.ofReal p := by simpa using hp.le
    have hlim := ((tendsto_eLpNorm_mollify_sub hϕ f hp.le).comp hδ).add
      ((tendsto_eLpNorm_mollify_atTop ϕ f hp).comp hR)
    rw [add_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) fun j => ?_
    have := eLpNorm_sub_le (μ := volume) hP
      (f := fun x => mollify ϕ f (1 / ((j : ℝ) + 1)) x - f x) (g := mollify ϕ f ((j : ℝ) + 1))
    refine le_trans (le_of_eq ?_) this
    congr 1
    funext x
    simp only [φ, sub_apply, Pi.sub_apply]
    ring
  · have hlim := ((tendsto_eLpNorm_fourier_mollify_sub hϕ f).comp hδ).add
      ((tendsto_eLpNorm_fourier_mollify_atTop ϕ f).comp hR)
    rw [add_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) fun j => ?_
    have := eLpNorm_sub_le (μ := volume) le_rfl
      (f := fun ξ => 𝓕 (mollify ϕ f (1 / ((j : ℝ) + 1))) ξ - 𝓕 f ξ)
      (g := 𝓕 (mollify ϕ f ((j : ℝ) + 1) : V → ℂ))
    refine le_trans (le_of_eq ?_) this
    congr 1
    funext ξ
    rw [← SchwartzMap.fourier_coe, Pi.sub_apply, hφ, fourier_mollify, fourier_mollify, hϕX, hX, hX]
    ring

end HarmonicAnalysis

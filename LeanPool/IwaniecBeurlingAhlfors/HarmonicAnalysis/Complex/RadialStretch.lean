/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Sobolev.Basic
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.RadialIntegral
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The radial stretch `z ↦ |z|^{α − 1} z`

For `0 < α ≤ 1`, the radial stretch `f (z) = |z|^{α − 1} z` (`f (re^{iθ}) = r^α e^{iθ}`) is the
extremal `K`-quasiconformal map for the higher integrability of the derivatives, `K = 1/α`:

* `HarmonicAnalysis.exists_homeomorph_radialStretch`: `f` is a homeomorphism of `ℂ` (its inverse
  is the radial stretch with exponent `1/α`);
* `HarmonicAnalysis.hasWeakFDerivOn_radialStretch`,
  `HarmonicAnalysis.memLpLoc_fderiv_radialStretch`: its pointwise derivative, which exists off
  `0`, is its weak derivative on `ℂ`, and is in `L²_loc (ℂ)`, so `f ∈ W^{1,2}_loc (ℂ)`;
* `HarmonicAnalysis.norm_dzbarPart_fderiv_radialStretch`: `|∂_zbar f| = ((1 − α)/(1 + α)) |∂f|`
off `0`,
  that is, `|∂_zbar f| = k |∂f|` with `k = (K − 1)/(K + 1)`;
* `HarmonicAnalysis.not_memLp_fderiv_radialStretch_apply_one`: for `α < 1`, `∂_x f` is not in
  `L^{2/(1 − α)}` of any disc around `0`; `2/(1 − α) = 2K/(K − 1)`.

Off `0`, `∂f = ((1 + α)/2) |z|^{α − 1}` and `∂_zbar f = ((α − 1)/2) |z|^{α − 1} z / (conj z)`
(`HarmonicAnalysis.dzPart_fderiv_radialStretch`, `HarmonicAnalysis.dzbarPart_fderiv_radialStretch`),
so `|Df| = |∂f| + |∂_zbar f| = |z|^{α − 1}`, which is in `L^p` near `0` if and only if
`(α − 1) p > −2`.

## Proofs

* The homeomorphism: `|f (z)| = |z|^α`, so the radial stretches with exponents `α` and `1/α` are
  inverse to each other (`HarmonicAnalysis.radialStretch_radialStretch`), and `f` is continuous at
  `0`.
* The derivative off `0`: `f (z) = (|z|²)^{(α − 1)/2} z`, and `|z|²` is smooth
  (`HarmonicAnalysis.fderiv_radialStretch_apply`).
* `|z|^t`, `−2 < t ≤ 0`, is integrable on compact sets: on the unit disc by
  `HarmonicAnalysis.lintegral_ball_norm_rpow`, and it is at most `1` off the unit disc.
* `L²_loc`: `‖Df (z)‖ ≤ |∂f| + |∂_zbar f| = |z|^{α − 1}`, and `2 (α − 1) > −2`.
* The weak derivative: `f` is the limit of the smooth maps `f_ε (z) = (|z|² + ε²)^{(α − 1)/2} z`,
  `ε → 0`, for which the integration by parts holds on the whole plane. On the support of a test
  function, `|f_ε (z)| ≤ |z|^α` and `|Df_ε (z) v| ≤ 2 |z|^{α − 1} |v|`, which is integrable, and
  dominated convergence passes to the limit on both sides (off the null set `{0}`).
* The failure of `L^{2/(1 − α)}`: `|∂_x f| ≥ |∂f| − |∂_zbar f| = α |z|^{α − 1}`, and
  `∫_{|z| < r} |z|^{−2} = 2π ∫_0^r ρ⁻¹ dρ = ∞` (`HarmonicAnalysis.lintegral_comp_norm`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff ComplexConjugate

namespace HarmonicAnalysis

/-- The radial stretch `z ↦ |z|^{α − 1} z` (`0` at `z = 0`). -/
def radialStretch (α : ℝ) (z : ℂ) : ℂ := (‖z‖ ^ (α - 1) : ℝ) • z

/-! ### The radial stretch as a homeomorphism -/

/-- `|f (z)| = |z|^α`, for `α ≠ 0`. -/
theorem norm_radialStretch {α : ℝ} (hα : α ≠ 0) (z : ℂ) : ‖radialStretch α z‖ = ‖z‖ ^ α := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [radialStretch, Real.zero_rpow hα]
  · rw [radialStretch, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _),
      ← Real.rpow_add_one (norm_ne_zero_iff.2 hz), sub_add_cancel]

/-- The radial stretches with exponents `α` and `β`, `αβ = 1`, are inverse to each other. -/
theorem radialStretch_radialStretch {α β : ℝ} (h : α * β = 1) (z : ℂ) :
    radialStretch β (radialStretch α z) = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [radialStretch]
  have hα : α ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [radialStretch, norm_radialStretch hα, radialStretch, smul_smul, ← Real.rpow_mul hz'.le,
    ← Real.rpow_add hz', show α * (β - 1) + (α - 1) = 0 by linear_combination h, Real.rpow_zero,
    one_smul]

/-- The radial stretch is continuous for `0 < α`, so it is in `L^p_loc (ℂ)` for every `p`. -/
theorem continuous_radialStretch {α : ℝ} (hα : 0 < α) : Continuous (radialStretch α) := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [ContinuousAt, show radialStretch α 0 = 0 by simp [radialStretch],
      tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_radialStretch hα.ne']
    have := ((continuous_norm (E := ℂ)).rpow_const fun _ => Or.inr hα.le).tendsto 0
    simpa [Real.zero_rpow hα.ne'] using this
  · exact (continuous_norm.continuousAt.rpow_const (Or.inl (norm_ne_zero_iff.2 hz))).smul
      continuousAt_id

/-- The radial stretch is a homeomorphism of `ℂ` for `0 < α`. -/
theorem exists_homeomorph_radialStretch {α : ℝ} (hα : 0 < α) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = radialStretch α :=
  ⟨{ toFun := radialStretch α
     invFun := radialStretch α⁻¹
     left_inv := radialStretch_radialStretch (mul_inv_cancel₀ hα.ne')
     right_inv := radialStretch_radialStretch (inv_mul_cancel₀ hα.ne')
     continuous_toFun := continuous_radialStretch hα
     continuous_invFun := continuous_radialStretch (inv_pos.2 hα) }, rfl⟩

/-! ### The derivative -/

/-- The smooth approximations `z ↦ (|z|² + ε²)^{(α − 1)/2} z` of the radial stretch. -/
private def rsReg (α ε : ℝ) (z : ℂ) : ℂ := ((‖z‖ ^ 2 + ε ^ 2) ^ ((α - 1) / 2) : ℝ) • z

private theorem rs_sq_rpow (α : ℝ) (z : ℂ) : (‖z‖ ^ 2) ^ ((α - 1) / 2) = ‖z‖ ^ (α - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
  congr 1
  push_cast
  ring

private theorem rsReg_zero (α : ℝ) : rsReg α 0 = radialStretch α := by
  funext z
  rw [rsReg, radialStretch, zero_pow two_ne_zero, add_zero, rs_sq_rpow]

private theorem rs_hasFDerivAt_reg (α ε : ℝ) {z : ℂ} (hz : ‖z‖ ^ 2 + ε ^ 2 ≠ 0) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (rsReg α ε) L z ∧ ∀ v, L v =
      ((‖z‖ ^ 2 + ε ^ 2) ^ ((α - 1) / 2) : ℝ) •
        (v + ((α - 1) * (z.re * v.re + z.im * v.im) / (‖z‖ ^ 2 + ε ^ 2) : ℝ) • z) := by
  have h1 := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)).rpow_const
    (p := (α - 1) / 2) (Or.inl hz)
  refine ⟨_, h1.smul (hasFDerivAt_id z), fun v => ?_⟩
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, Complex.inner]
  rw [Real.rpow_sub_one hz, smul_add, smul_smul]
  congr 1
  congr 1
  simp only [smul_eq_mul, nsmul_eq_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

private theorem rs_fderiv_reg_apply (α ε : ℝ) {z : ℂ} (hz : ‖z‖ ^ 2 + ε ^ 2 ≠ 0) (v : ℂ) :
    fderiv ℝ (rsReg α ε) z v = ((‖z‖ ^ 2 + ε ^ 2) ^ ((α - 1) / 2) : ℝ) •
      (v + ((α - 1) * (z.re * v.re + z.im * v.im) / (‖z‖ ^ 2 + ε ^ 2) : ℝ) • z) := by
  obtain ⟨L, hL, hLv⟩ := rs_hasFDerivAt_reg α ε hz
  rw [hL.fderiv, hLv]

/-- The derivative of the radial stretch off `0`:
`Df (z) v = |z|^{α − 1} (v + (α − 1) ⟨z, v⟩ / |z|² z)`. -/
theorem fderiv_radialStretch_apply (α : ℝ) {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    fderiv ℝ (radialStretch α) z v =
      (‖z‖ ^ (α - 1) : ℝ) • (v + ((α - 1) * (z.re * v.re + z.im * v.im) / ‖z‖ ^ 2 : ℝ) • z) := by
  have h : ‖z‖ ^ 2 + 0 ^ 2 ≠ 0 := by
    rw [zero_pow two_ne_zero, add_zero]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hz)
  rw [← rsReg_zero, rs_fderiv_reg_apply α 0 h, zero_pow two_ne_zero, add_zero, rs_sq_rpow]

private theorem rs_norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- `∂f = ((1 + α)/2) |z|^{α − 1}` off `0`. -/
theorem dzPart_fderiv_radialStretch (α : ℝ) {z : ℂ} (hz : z ≠ 0) :
    dzPart (fderiv ℝ (radialStretch α) z) = ((1 + α) / 2 * ‖z‖ ^ (α - 1) : ℝ) := by
  have hN : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
    rw [← rs_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hz)
  simp only [dzPart, fderiv_radialStretch_apply α hz, rs_norm_sq]
  apply Complex.ext <;>
  · simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.inv_re,
      Complex.inv_im, Complex.normSq_ofNat, Complex.re_ofNat, Complex.im_ofNat]
    field_simp
    ring

/-- `∂_zbar f = ((α − 1)/2) |z|^{α − 1} z / (conj z)` off `0`. -/
theorem dzbarPart_fderiv_radialStretch (α : ℝ) {z : ℂ} (hz : z ≠ 0) :
    dzbarPart (fderiv ℝ (radialStretch α) z) =
      ((α - 1) / 2 * ‖z‖ ^ (α - 1) : ℝ) * (z / conj z) := by
  have hN : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
    rw [← rs_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hz)
  have hzz : z / conj z = z ^ 2 / ((z.re ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
    rw [← rs_norm_sq, Complex.ofReal_pow, ← Complex.mul_conj']
    have hc : conj z ≠ 0 := (map_ne_zero _).2 hz
    field_simp
  simp only [dzbarPart, fderiv_radialStretch_apply α hz, rs_norm_sq, hzz]
  apply Complex.ext <;>
  · simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, Complex.inv_re, Complex.inv_im, Complex.normSq_ofNat,
      Complex.re_ofNat, Complex.im_ofNat, Complex.div_ofReal_re, Complex.div_ofReal_im, pow_two]
    field_simp
    ring

/-- `|∂f| = ((1 + α)/2) |z|^{α − 1}` off `0`, for `−1 ≤ α`. -/
private theorem rs_norm_dzPart {α : ℝ} (hα : -1 ≤ α) {z : ℂ} (hz : z ≠ 0) :
    ‖dzPart (fderiv ℝ (radialStretch α) z)‖ = (1 + α) / 2 * ‖z‖ ^ (α - 1) := by
  rw [dzPart_fderiv_radialStretch α hz, Complex.norm_real, Real.norm_of_nonneg]
  have := Real.rpow_nonneg (norm_nonneg z) (α - 1)
  have : 0 ≤ (1 + α) / 2 := by linarith
  positivity

/-- `|∂_zbar f| = ((1 − α)/2) |z|^{α − 1}` off `0`, for `α ≤ 1`. -/
private theorem rs_norm_dzbarPart {α : ℝ} (hα1 : α ≤ 1) {z : ℂ} (hz : z ≠ 0) :
    ‖dzbarPart (fderiv ℝ (radialStretch α) z)‖ = (1 - α) / 2 * ‖z‖ ^ (α - 1) := by
  rw [dzbarPart_fderiv_radialStretch α hz, norm_mul, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.2 hz), mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), abs_div, abs_two,
    abs_of_nonpos (by linarith : α - 1 ≤ 0)]
  ring

/-- `|∂_zbar f| = ((1 − α)/(1 + α)) |∂f|` off `0`, for `α ≤ 1`. -/
theorem norm_dzbarPart_fderiv_radialStretch {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℂ}
    (hz : z ≠ 0) :
    ‖dzbarPart (fderiv ℝ (radialStretch α) z)‖ =
      (1 - α) / (1 + α) * ‖dzPart (fderiv ℝ (radialStretch α) z)‖ := by
  rw [rs_norm_dzbarPart hα1 hz, rs_norm_dzPart (by linarith) hz]
  field_simp

/-- `‖Df (z)‖ ≤ |z|^{α − 1}` off `0`, for `0 < α ≤ 1`. -/
private theorem rs_norm_fderiv_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ (radialStretch α) z‖ ≤ ‖z‖ ^ (α - 1) := by
  refine (norm_le_dzPart_add_dzbarPart _).trans (le_of_eq ?_)
  rw [rs_norm_dzbarPart hα1 hz, rs_norm_dzPart (by linarith) hz]
  ring

/-- `|∂_x f (z)| ≥ α |z|^{α − 1}` off `0`, for `0 < α ≤ 1`. -/
private theorem rs_le_norm_fderiv_apply_one {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℂ}
    (hz : z ≠ 0) : α * ‖z‖ ^ (α - 1) ≤ ‖fderiv ℝ (radialStretch α) z 1‖ := by
  have h := apply_eq_dzPart_add_dzbarPart (fderiv ℝ (radialStretch α) z) 1
  rw [mul_one, (starRingEnd ℂ).map_one, mul_one] at h
  have h' := norm_sub_le (fderiv ℝ (radialStretch α) z 1)
    (dzbarPart (fderiv ℝ (radialStretch α) z))
  rw [h, add_sub_cancel_right, rs_norm_dzbarPart hα1 hz, rs_norm_dzPart (by linarith) hz] at h'
  rw [h]
  linarith

/-! ### Integrability of `|z|^t` near `0` -/

private theorem rs_ae_ne_zero : ∀ᵐ z : ℂ, z ≠ 0 := by
  simp [ae_iff, measure_singleton]

/-- `|z|^t` is integrable on compact sets, for `−2 < t ≤ 0`. -/
private theorem rs_integrableOn_norm_rpow {t : ℝ} (ht : -2 < t) (ht0 : t ≤ 0) {K : Set ℂ}
    (hK : IsCompact K) : IntegrableOn (fun z : ℂ => ‖z‖ ^ t) K := by
  have hmeas : Measurable fun z : ℂ => ‖z‖ ^ t := by fun_prop
  have hball : IntegrableOn (fun z : ℂ => ‖z‖ ^ t) (Metric.ball 0 1) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg z) t)]
    have h := lintegral_ball_norm_rpow (s := -t) (by linarith)
    rw [neg_neg] at h
    rw [h]
    exact ENNReal.ofReal_lt_top
  have hsum : IntegrableOn
      (fun z : ℂ => (Metric.ball (0 : ℂ) 1).indicator (fun z => ‖z‖ ^ t) z + 1) K :=
    ((integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 hball).integrableOn.add
      (integrableOn_const hK.measure_lt_top.ne)
  refine hsum.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) t)]
  by_cases hz : ‖z‖ < 1
  · rw [Set.indicator_of_mem (mem_ball_zero_iff.2 hz)]
    linarith
  · rw [Set.indicator_of_notMem (mt mem_ball_zero_iff.1 hz), zero_add]
    exact Real.rpow_le_one_of_one_le_of_nonpos (not_lt.1 hz) ht0

/-- `|z|^t` is locally integrable, for `−2 < t ≤ 0`. -/
private theorem rs_locallyIntegrable_norm_rpow {t : ℝ} (ht : -2 < t) (ht0 : t ≤ 0) :
    LocallyIntegrable (fun z : ℂ => ‖z‖ ^ t) :=
  locallyIntegrable_iff.2 fun _ hK => rs_integrableOn_norm_rpow ht ht0 hK

/-- `|z|^{−2}` is not integrable on any disc around `0`. -/
private theorem rs_not_integrableOn_ball {r : ℝ} (hr : 0 < r) :
    ¬ IntegrableOn (fun z : ℂ => ‖z‖ ^ (-2 : ℝ)) (Metric.ball 0 r) := by
  intro h
  have hfin : ∫⁻ z in Metric.ball (0 : ℂ) r, ENNReal.ofReal (‖z‖ ^ (-2 : ℝ)) < (∞ : ℝ≥0∞) :=
    (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg z) _)).1 h.2
  set g : ℝ → ℝ≥0∞ := (Set.Iio r).indicator fun t => ENNReal.ofReal (t ^ (-2 : ℝ)) with g_def
  have hg : Measurable g :=
    (by fun_prop : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (-2 : ℝ))).indicator
      measurableSet_Iio
  have hball : (Metric.ball (0 : ℂ) r).indicator (fun z => ENNReal.ofReal (‖z‖ ^ (-2 : ℝ))) =
      fun z => g ‖z‖ := by
    funext z
    by_cases hz : ‖z‖ < r
    · rw [g_def, Set.indicator_of_mem (mem_ball_zero_iff.2 hz),
        Set.indicator_of_mem (Set.mem_Iio.2 hz)]
    · rw [g_def, Set.indicator_of_notMem (mt mem_ball_zero_iff.1 hz),
        Set.indicator_of_notMem (mt Set.mem_Iio.1 hz)]
  have hmul : (fun t => ENNReal.ofReal t * g t) =
      (Set.Iio r).indicator fun t => ENNReal.ofReal t * ENNReal.ofReal (t ^ (-2 : ℝ)) := by
    funext t
    simp only [g_def, Set.indicator_apply]
    split_ifs <;> simp
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet, hball, lintegral_comp_norm hg,
    hmul, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Set.inter_comm, Set.Ioi_inter_Iio,
    setLIntegral_congr_fun measurableSet_Ioo (g := fun t => ENNReal.ofReal (t ^ (-1 : ℝ)))
      (fun t ht => by
        dsimp only
        rw [← ENNReal.ofReal_mul ht.1.le, show (-1 : ℝ) = 1 + -2 by norm_num,
          Real.rpow_add ht.1, Real.rpow_one])] at hfin
  have hfin' := ENNReal.lt_top_of_mul_ne_top_right hfin.ne
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  refine (intervalIntegral.integrableOn_Ioo_rpow_iff hr).not.2 (lt_irrefl _) ⟨by fun_prop, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem measurableSet_Ioo
    fun t ht => Real.rpow_nonneg ht.1.le _)).2 hfin'

/-! ### The weak derivative -/

private theorem rs_contDiff_reg (α : ℝ) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (rsReg α ε) := by
  have h : ContDiff ℝ 1 fun z : ℂ => ‖z‖ ^ 2 + ε ^ 2 := (contDiff_norm_sq ℝ).add contDiff_const
  exact (h.rpow_const_of_ne fun z => by positivity).smul contDiff_id

/-- `|f_ε (z)| ≤ |z|^α` off `0`, for `α ≤ 1`. -/
private theorem rs_norm_reg_le {α : ℝ} (hα1 : α ≤ 1) (ε : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖rsReg α ε z‖ ≤ ‖z‖ ^ α := by
  have hz2 : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  have hM : ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 + ε ^ 2 := le_add_of_nonneg_right (sq_nonneg ε)
  rw [rsReg, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (hz2.le.trans hM) _)]
  calc _ ≤ ‖z‖ ^ (α - 1) * ‖z‖ := by
        gcongr
        rw [← rs_sq_rpow]
        exact Real.rpow_le_rpow_of_nonpos hz2 hM (by linarith)
    _ = ‖z‖ ^ α := by rw [← Real.rpow_add_one (norm_ne_zero_iff.2 hz), sub_add_cancel]

/-- `|Df_ε (z) v| ≤ 2 |z|^{α − 1} |v|` off `0`, for `0 ≤ α ≤ 1`. -/
private theorem rs_norm_fderiv_reg_le {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (ε : ℝ) {z : ℂ}
    (hz : z ≠ 0) (v : ℂ) : ‖fderiv ℝ (rsReg α ε) z v‖ ≤ 2 * ‖v‖ * ‖z‖ ^ (α - 1) := by
  have hz2 : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  have hM : ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 + ε ^ 2 := le_add_of_nonneg_right (sq_nonneg ε)
  have hMpos : 0 < ‖z‖ ^ 2 + ε ^ 2 := hz2.trans_le hM
  have hip : |z.re * v.re + z.im * v.im| ≤ ‖z‖ * ‖v‖ := by
    have h := Complex.abs_re_le_norm (conj z * v)
    rwa [norm_mul, Complex.norm_conj, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul,
      sub_neg_eq_add] at h
  have hα' : |α - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have h1 : ‖v + ((α - 1) * (z.re * v.re + z.im * v.im) / (‖z‖ ^ 2 + ε ^ 2) : ℝ) • z‖ ≤
      2 * ‖v‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hMpos]
    have h2 : |α - 1| * |z.re * v.re + z.im * v.im| / (‖z‖ ^ 2 + ε ^ 2) * ‖z‖ ≤ ‖v‖ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hMpos]
      calc |α - 1| * |z.re * v.re + z.im * v.im| * ‖z‖ ≤ 1 * (‖z‖ * ‖v‖) * ‖z‖ := by gcongr
        _ = ‖v‖ * ‖z‖ ^ 2 := by ring
        _ ≤ ‖v‖ * (‖z‖ ^ 2 + ε ^ 2) := by gcongr
    linarith
  have h3 : (‖z‖ ^ 2 + ε ^ 2) ^ ((α - 1) / 2) ≤ ‖z‖ ^ (α - 1) := by
    rw [← rs_sq_rpow]
    exact Real.rpow_le_rpow_of_nonpos hz2 hM (by linarith)
  rw [rs_fderiv_reg_apply α ε hMpos.ne' v, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg hMpos.le _)]
  calc _ ≤ ‖z‖ ^ (α - 1) * (2 * ‖v‖) :=
        mul_le_mul h3 h1 (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
    _ = 2 * ‖v‖ * ‖z‖ ^ (α - 1) := by ring

/-- `f_ε (z) → f (z)` as `ε → 0`, for `z ≠ 0`. -/
private theorem rs_tendsto_reg (α : ℝ) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {z : ℂ}
    (hz : z ≠ 0) : Tendsto (fun n => rsReg α (ε n) z) atTop (𝓝 (radialStretch α z)) := by
  have hN : ‖z‖ ^ 2 + (0 : ℝ) ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.2 hz) 2) (sq_nonneg 0)).ne'
  have hc : ContinuousAt (fun e : ℝ => ((‖z‖ ^ 2 + e ^ 2) ^ ((α - 1) / 2) : ℝ) • z) 0 :=
    ((continuousAt_const.add (continuousAt_id.pow 2)).rpow_const (Or.inl hN)).smul
      continuousAt_const
  rw [← rsReg_zero]
  exact hc.tendsto.comp hε

/-- `Df_ε (z) v → Df (z) v` as `ε → 0`, for `z ≠ 0`. -/
private theorem rs_tendsto_fderiv_reg (α : ℝ) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    Tendsto (fun n => fderiv ℝ (rsReg α (ε n)) z v) atTop
      (𝓝 (fderiv ℝ (radialStretch α) z v)) := by
  have hpos : ∀ e : ℝ, ‖z‖ ^ 2 + e ^ 2 ≠ 0 := fun e =>
    (add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.2 hz) 2) (sq_nonneg e)).ne'
  have hc : ContinuousAt (fun e : ℝ => ((‖z‖ ^ 2 + e ^ 2) ^ ((α - 1) / 2) : ℝ) •
      (v + ((α - 1) * (z.re * v.re + z.im * v.im) / (‖z‖ ^ 2 + e ^ 2) : ℝ) • z)) 0 :=
    ((continuousAt_const.add (continuousAt_id.pow 2)).rpow_const (Or.inl (hpos 0))).smul
      (continuousAt_const.add ((continuousAt_const.div
        (continuousAt_const.add (continuousAt_id.pow 2)) (hpos 0)).smul continuousAt_const))
  have h1 : (fun n => fderiv ℝ (rsReg α (ε n)) z v) = fun n =>
      ((‖z‖ ^ 2 + ε n ^ 2) ^ ((α - 1) / 2) : ℝ) •
        (v + ((α - 1) * (z.re * v.re + z.im * v.im) / (‖z‖ ^ 2 + ε n ^ 2) : ℝ) • z) :=
    funext fun n => rs_fderiv_reg_apply α _ (hpos _) v
  rw [h1, ← rsReg_zero, rs_fderiv_reg_apply α 0 (hpos 0) v]
  exact hc.tendsto.comp hε

/-- The integration by parts for the smooth approximations `f_ε`, `ε > 0`. -/
private theorem rs_integral_reg (α : ℝ) {ε : ℝ} (hε : 0 < ε) (v : ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, fderiv ℝ φ x v • rsReg α ε x = -∫ x, φ x • fderiv ℝ (rsReg α ε) x v := by
  have hg := rs_contDiff_reg α hε
  have hgd : Differentiable ℝ (rsReg α ε) := hg.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hDφ : Continuous fun x => fderiv ℝ φ x v :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDg : Continuous fun x => fderiv ℝ (rsReg α ε) x v :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    ((hDφ.smul hg.continuous).integrable_of_hasCompactSupport
      (hφc.fderiv_apply (𝕜 := ℝ) v).smul_right)
    ((hφ.continuous.smul hDg).integrable_of_hasCompactSupport hφc.smul_right)
    ((hφ.continuous.smul hg.continuous).integrable_of_hasCompactSupport hφc.smul_right)
    (fun x _ => hφd x) (fun x _ => hgd x), neg_neg]

/-- The pointwise derivative of the radial stretch (`0` at `z = 0`) is its weak derivative on the
whole plane, for `0 < α ≤ 1`. -/
theorem hasWeakFDerivOn_radialStretch {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    HasWeakFDerivOn Set.univ (radialStretch α) (fderiv ℝ (radialStretch α)) := by
  intro v φ hφ hφc _
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hDφ : Continuous fun x => fderiv ℝ φ x v :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  -- the left-hand sides converge, dominated by `|∂_v φ (x)| |x|^α`
  have hL : Tendsto (fun n => ∫ x, fderiv ℝ φ x v • rsReg α (ε n) x) atTop
      (𝓝 (∫ x, fderiv ℝ φ x v • radialStretch α x)) := by
    have hb : Continuous fun x : ℂ => ‖fderiv ℝ φ x v‖ * ‖x‖ ^ α :=
      hDφ.norm.mul (continuous_norm.rpow_const fun _ => Or.inr hα.le)
    have hint : Integrable fun x : ℂ => ‖fderiv ℝ φ x v‖ * ‖x‖ ^ α :=
      hb.integrable_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) v).norm.mul_right
    refine tendsto_integral_of_dominated_convergence _
      (fun n => (hDφ.smul (rs_contDiff_reg α (hε n)).continuous).aestronglyMeasurable) hint
      (fun n => ?_) ?_
    · filter_upwards [rs_ae_ne_zero] with x hx
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (rs_norm_reg_le hα1 _ hx) (norm_nonneg _)
    · filter_upwards [rs_ae_ne_zero] with x hx
      exact tendsto_const_nhds.smul (rs_tendsto_reg α hε0 hx)
  -- the right-hand sides converge, dominated by `2 |v| |φ (x)| |x|^{α − 1}`
  have hR : Tendsto (fun n => ∫ x, φ x • fderiv ℝ (rsReg α (ε n)) x v) atTop
      (𝓝 (∫ x, φ x • fderiv ℝ (radialStretch α) x v)) := by
    have hint : Integrable fun x : ℂ => φ x • ‖x‖ ^ (α - 1) :=
      sob_integrable_smul_of_tsupport_subset
        ((rs_locallyIntegrable_norm_rpow (t := α - 1) (by linarith)
          (by linarith)).locallyIntegrableOn Set.univ)
        hφ.continuous hφc (Set.subset_univ _)
    refine tendsto_integral_of_dominated_convergence
      (fun x => 2 * ‖v‖ * ‖φ x • ‖x‖ ^ (α - 1)‖)
      (fun n => hφ.continuous.aestronglyMeasurable.smul
        (measurable_fderiv_apply_const ℝ _ v).aestronglyMeasurable)
      (hint.norm.const_mul _) (fun n => ?_) ?_
    · filter_upwards [rs_ae_ne_zero] with x hx
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
      calc ‖φ x‖ * ‖fderiv ℝ (rsReg α (ε n)) x v‖ ≤ ‖φ x‖ * (2 * ‖v‖ * ‖x‖ ^ (α - 1)) :=
            mul_le_mul_of_nonneg_left (rs_norm_fderiv_reg_le hα.le hα1 _ hx v) (norm_nonneg _)
        _ = _ := by ring
    · filter_upwards [rs_ae_ne_zero] with x hx
      exact tendsto_const_nhds.smul (rs_tendsto_fderiv_reg α hε0 hx v)
  have heq : (fun n => ∫ x, fderiv ℝ φ x v • rsReg α (ε n) x) =
      fun n => -∫ x, φ x • fderiv ℝ (rsReg α (ε n)) x v :=
    funext fun n => rs_integral_reg α (hε n) v hφ hφc
  rw [heq] at hL
  exact tendsto_nhds_unique hL hR.neg

/-- The derivative of the radial stretch is in `L²_loc (ℂ)`, for `0 < α ≤ 1`. -/
theorem memLpLoc_fderiv_radialStretch {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    MemLpLoc (fderiv ℝ (radialStretch α)) 2 Set.univ := by
  intro K _ hK
  have hg : MemLp (fun z : ℂ => ‖z‖ ^ (α - 1)) 2 (volume.restrict K) := by
    rw [memLp_two_iff_integrable_sq
      (by fun_prop : Measurable fun z : ℂ => ‖z‖ ^ (α - 1)).aestronglyMeasurable]
    have h := rs_integrableOn_norm_rpow (t := 2 * (α - 1)) (by linarith) (by linarith) hK
    refine h.congr_fun (fun z _ => ?_) hK.measurableSet
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z), Nat.cast_ofNat, mul_comm]
  refine hg.of_le (measurable_fderiv ℝ _).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae rs_ae_ne_zero] with z hz
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  exact rs_norm_fderiv_le hα hα1 hz

/-- For `0 < α < 1`, `∂_x f` is not in `L^{2/(1 − α)}` of any disc around `0`. -/
theorem not_memLp_fderiv_radialStretch_apply_one {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {r : ℝ}
    (hr : 0 < r) :
    ¬ MemLp (fun z => fderiv ℝ (radialStretch α) z 1) (ENNReal.ofReal (2 / (1 - α)))
      (volume.restrict (Metric.ball 0 r)) := by
  intro h
  set p : ℝ := 2 / (1 - α) with hp_def
  have hp : 0 < p := div_pos two_pos (by linarith)
  have hint := h.integrable_norm_rpow (by simp [hp]) ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp.le] at hint
  apply rs_not_integrableOn_ball hr
  refine (hint.const_mul (α ^ p)⁻¹).mono'
    (by fun_prop : Measurable fun z : ℂ => ‖z‖ ^ (-2 : ℝ)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae rs_ae_ne_zero] with z hz
  have hαp : 0 < α ^ p := Real.rpow_pos_of_pos hα p
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hz'.le _), le_inv_mul_iff₀ hαp]
  have h1 : α ^ p * ‖z‖ ^ (-2 : ℝ) = (α * ‖z‖ ^ (α - 1)) ^ p := by
    rw [Real.mul_rpow hα.le (Real.rpow_nonneg hz'.le _), ← Real.rpow_mul hz'.le]
    congr 2
    rw [hp_def]
    field_simp
    ring
  rw [h1]
  exact Real.rpow_le_rpow (by positivity) (rs_le_norm_fderiv_apply_one hα hα1.le hz) hp.le

end HarmonicAnalysis

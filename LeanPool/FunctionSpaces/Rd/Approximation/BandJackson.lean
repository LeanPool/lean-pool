/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Differences.MomentKernels
public import LeanPool.FunctionSpaces.Rd.Approximation.BandLimited
public import LeanPool.FunctionSpaces.ApproximationSpaces.Norm

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Jackson's inequality for band-limited approximation

For `f ∈ L_p(V)`, `1 ≤ p < ∞`, and `r, k ∈ ℕ` the **Jackson approximant** is

`J_k f = ∑_{l=1}^r (-1)^(l+1) C(r, l) Φ_{2^k/l} ⋆ f`

(`Rd.jacksonApprox`), with the Littlewood–Paley kernel `Φ` of `Rd.lpKernel` and its dilations
`Φ_c = c^n Φ(c ·)`. The transform of `Φ_{2^k/l}` lives in the ball of radius `2^(k+1)/l`, where
`𝓕Θ_k = 1`, so `Θ_k ⋆ Φ_{2^k/l} = Φ_{2^k/l}` and `J_k f ∈ E_k` (`Rd.jacksonApprox_mem_bandSpace`).
Since `∫ Φ = 1`, the averaged differences of the moment kernels (`Rd.ae_sub_sum_conv_dilate_eq`)
give

`f(x) - J_k f(x) = ∫ Φ(z) (-1)^r Δ^r_{-2^(-k) z} f(x) dz`

for almost every `x` (`Rd.ae_sub_jacksonApprox_eq`). The weighted Jensen inequality
(`MeasureTheory.eLpNorm_integral_kernel_le`, `Rd.eLpNorm_integral_lpKernel_mul_le`) and
`ω_r(f, 2^(-k) |z|)_p ≤ (1 + |z|)^r ω_r(f, 2^(-k))_p` give
**Jackson's inequality** (`Rd.enorm_sub_jacksonApprox_le`, `Rd.approxError_bandScheme_le`)

`E(f, E_k)_p ≤ ‖f - J_k f‖_p ≤ C ω_r(f, 2^(-k))_p`,
`C^p = ‖Φ‖_1^(p-1) ∫ |Φ(z)| (1 + |z|)^(rp) dz`,

with `C` finite because `Φ` is a Schwartz function (`Rd.jacksonConst_ne_top`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal FourierTransform

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The kernels of the Jackson approximant -/

/-- **Band-limited dilations of the Littlewood–Paley kernel**: `Θ_k ⋆ Φ_c = Φ_c` for
`0 < c ≤ 2^k`, since `𝓕Φ_c = χ_{1,2}(c^(-1) ·)` lives in the ball of radius `2c ≤ 2^(k+1)`. -/
theorem conv_Theta_dilate_lpKernel {k : ℕ} {c : ℝ} (hc : 0 < c) (hck : c ≤ 2 ^ k) :
    conv (Theta (V := V) k) (dilate c lpKernel) volume = dilate c lpKernel := by
  refine conv_eq_of_fourier (integrable_Theta k) (integrable_dilate integrable_lpKernel hc.ne')
    (continuous_dilate continuous_lpKernel c) (bddAbove_dilate bddAbove_lpKernel c)
    (integrable_dilate integrable_lpKernel hc.ne') (continuous_dilate continuous_lpKernel c)
    (integrable_fourier_dilate integrable_fourier_lpKernel hc) fun ξ => ?_
  by_cases h : 𝓕 (dilate c (lpKernel (V := V))) ξ = 0
  · rw [h, mul_zero]
  · have hξ : ‖ξ‖ ≤ 2 ^ (k + 1) := by
      rw [fourier_dilate _ hc, fourier_lpKernel] at h
      have h1 := norm_lt_of_cutoff_ne_zero _ _ h
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le, inv_mul_lt_iff₀ hc] at h1
      rw [pow_succ]
      linarith
    rw [fourier_Theta_eq_one hξ, one_mul]

/-- The scales `2^k / (l + 1)` of the Jackson approximant. -/
noncomputable def jacksonScale (k l : ℕ) : ℝ := 2 ^ k / (l + 1)

/-- The scales are positive. -/
theorem jacksonScale_pos (k l : ℕ) : 0 < jacksonScale k l := by
  unfold jacksonScale
  positivity

/-- The scales are at most `2^k`. -/
theorem jacksonScale_le (k l : ℕ) : jacksonScale k l ≤ 2 ^ k := by
  unfold jacksonScale
  exact div_le_self (by positivity) (by linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)])

/-! ### The Jackson approximant -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **Jackson approximant** `J_k f = ∑_{l<r} (-1)^l C(r, l + 1) Φ_{2^k/(l+1)} ⋆ f`. -/
noncomputable def jacksonApprox (hp : p ≠ ∞) (r k : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure V) :=
  ∑ l ∈ Finset.range r, jacksonCoeff r l •
    convLp hp (integrable_dilate integrable_lpKernel (jacksonScale_pos k l).ne') f

/-- **The Jackson approximant is band-limited**: `J_k f ∈ E_k`. -/
theorem jacksonApprox_mem_bandSpace (hp : p ≠ ∞) (r k : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    jacksonApprox hp r k f ∈ bandSpace hp k := by
  refine Submodule.sum_mem _ fun l _ => smul_mem_bandSpace _ ?_
  rw [mem_bandSpace]
  exact convLp_convLp_of_eq hp _ _ _
    (conv_Theta_dilate_lpKernel (jacksonScale_pos k l) (jacksonScale_le k l)) f

/-- **The Jackson approximant as an averaged difference**: for almost every `x`,
`f(x) - J_k f(x) = ∫ Φ(z) (-1)^r Δ^r_{-2^(-k) z} f(x) dz`. -/
theorem ae_sub_jacksonApprox_eq (hp : p ≠ ∞) (r k : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ⇑(f - jacksonApprox hp r k f) =ᵐ[volume] fun x => ∫ z, lpKernel z *
      ((-1 : ℂ) ^ r * (fwdDiff (-((2 : ℝ) ^ k)⁻¹ • z))^[r] (f : V → ℂ) x) := by
  have hJ : ⇑(jacksonApprox hp r k f) =ᵐ[volume] fun x => ∑ l ∈ Finset.range r,
      jacksonCoeff r l * conv (dilate (jacksonScale k l) lpKernel) (f : V → ℂ) volume x := by
    unfold jacksonApprox
    refine (Lp.coeFn_finsetSum _ _).trans ((eventuallyEq_sum fun l _ =>
      (Lp.coeFn_smul _ _).trans ((convLp_apply_ae hp (integrable_dilate integrable_lpKernel
        (jacksonScale_pos k l).ne') f).const_smul (jacksonCoeff r l))).trans (.of_eq ?_))
    funext x
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [Pi.smul_apply, smul_eq_mul]
  filter_upwards [Lp.coeFn_sub f (jacksonApprox hp r k f), hJ,
    ae_sub_sum_conv_dilate_eq Fact.out hp integrable_lpKernel integral_lpKernel (Lp.memLp f) r
      (c := (2 : ℝ) ^ k) (by positivity)] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2]
  exact h3

/-! ### Jackson's inequality -/

variable (V) in
/-- The **constant of Jackson's inequality**,
`C = (‖Φ‖_1^(p-1) ∫ |Φ(z)| (1 + |z|)^(rp) dz)^(1/p)`. -/
noncomputable def jacksonConst (r : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ((∫⁻ z, ‖lpKernel (V := V) z‖ₑ) ^ (p.toReal - 1) *
    ∫⁻ z, ‖lpKernel (V := V) z‖ₑ * ENNReal.ofReal (1 + ‖z‖) ^ ((r : ℝ) * p.toReal)) ^
      (1 / p.toReal)

omit [Fact (1 ≤ p)] in
/-- **The constant of Jackson's inequality is finite**: `Φ` decays faster than every power,
`|Φ(z)| (1 + |z|)^(rp) ≤ 2^N (|Φ(z)| + |z|^N |Φ(z)|)` with `N = ⌈rp⌉`. -/
theorem jacksonConst_ne_top (hp1 : 1 ≤ p) (hp : p ≠ ∞) (r : ℕ) : jacksonConst V r p ≠ ∞ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  have h1 : ∫⁻ z, ‖lpKernel (V := V) z‖ₑ ≠ ∞ := integrable_lpKernel.2.ne
  set N := ⌈(r : ℝ) * p.toReal⌉₊
  have hint : Integrable (fun z : V => 2 ^ N * (‖lpKernel z‖ + ‖z‖ ^ N * ‖lpKernel z‖)) :=
    (integrable_lpKernel.norm.add
      (SchwartzMap.integrable_pow_mul volume (lpKernelS (V := V)) N)).const_mul _
  have h2 : ∫⁻ z, ‖lpKernel (V := V) z‖ₑ * ENNReal.ofReal (1 + ‖z‖) ^ ((r : ℝ) * p.toReal) ≠
      ∞ := by
    refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne (lintegral_mono fun z => ?_)
    have hz : 0 ≤ (1 : ℝ) + ‖z‖ := by positivity
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg hz (by positivity),
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpow : (1 + ‖z‖) ^ ((r : ℝ) * p.toReal) ≤ (1 + ‖z‖) ^ N := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (Nat.le_ceil _)
    calc ‖lpKernel z‖ * (1 + ‖z‖) ^ ((r : ℝ) * p.toReal)
        ≤ ‖lpKernel z‖ * (2 ^ N * (1 + ‖z‖ ^ N)) := by
          gcongr
          exact hpow.trans (one_add_pow_le_two_pow_mul (norm_nonneg z) N)
      _ = 2 ^ N * (‖lpKernel z‖ + ‖z‖ ^ N * ‖lpKernel z‖) := by ring
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) h1) h2)

omit [Fact (1 ≤ p)] in
/-- **Weighted averages with the Jackson weight**: for `1 ≤ p < ∞`, `r ∈ ℕ`, an s-finite measure
space `(α, μ)`, `M < ∞` and a jointly measurable `G : α × V → ℂ` with
`‖G(·, z)‖_p ≤ (1 + |z|)^r M` for every `z`, `‖∫ Φ(z) G(·, z) dz‖_p ≤ C M` with the constant
`C = Rd.jacksonConst V r p` of Jackson's inequality, by the weighted averages of
`MeasureTheory.eLpNorm_integral_kernel_le`. It gives Jackson's inequality on `V` and on the
torus. -/
theorem eLpNorm_integral_lpKernel_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] (hp1 : 1 ≤ p) (hp : p ≠ ∞) (r : ℕ) {G : α → V → ℂ}
    (hG : Measurable (Function.uncurry G)) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbound : ∀ z, eLpNorm (fun x => G x z) p μ ≤ ENNReal.ofReal (1 + ‖z‖) ^ r * M) :
    eLpNorm (fun x => ∫ z, lpKernel z * G x z) p μ ≤ jacksonConst V r p * M := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one hp1).ne' hp
  rw [← ENNReal.rpow_le_rpow_iff hq]
  refine (eLpNorm_integral_kernel_le hp1 hp integrable_lpKernel.aestronglyMeasurable hG).trans ?_
  calc (∫⁻ z, ‖lpKernel (V := V) z‖ₑ) ^ (p.toReal - 1) *
        ∫⁻ z, ‖lpKernel z‖ₑ * eLpNorm (fun x => G x z) p μ ^ p.toReal
      ≤ (∫⁻ z, ‖lpKernel (V := V) z‖ₑ) ^ (p.toReal - 1) *
          ∫⁻ z, ‖lpKernel z‖ₑ * (ENNReal.ofReal (1 + ‖z‖) ^ ((r : ℝ) * p.toReal) *
            M ^ p.toReal) := by
        gcongr with z
        calc eLpNorm (fun x => G x z) p μ ^ p.toReal
            ≤ (ENNReal.ofReal (1 + ‖z‖) ^ r * M) ^ p.toReal :=
              ENNReal.rpow_le_rpow (hbound z) hq.le
          _ = ENNReal.ofReal (1 + ‖z‖) ^ ((r : ℝ) * p.toReal) * M ^ p.toReal := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_natCast,
                ← ENNReal.rpow_mul]
    _ = (jacksonConst V r p * M) ^ p.toReal := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, jacksonConst, ← ENNReal.rpow_mul,
          one_div_mul_cancel hq.ne', ENNReal.rpow_one, mul_assoc]
        congr 1
        rw [← lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le hM)]
        exact lintegral_congr fun z => by ring

/-- **Jackson's inequality for band-limited approximation**: for `f ∈ L_p`, `1 ≤ p < ∞`,
`‖f - J_k f‖_p ≤ C ω_r(f, 2^(-k))_p`, from `‖Δ^r_{-2^(-k) z} f‖_p ≤ (1 + |z|)^r ω_r(f, 2^(-k))_p`
(`Rd.eLpNorm_integral_lpKernel_mul_le`). -/
theorem enorm_sub_jacksonApprox_le (hp : p ≠ ∞) (r k : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ‖f - jacksonApprox hp r k f‖ₑ ≤ jacksonConst V r p * lpModulus p r f k := by
  have hp1 : 1 ≤ p := Fact.out
  have hfm : Measurable (f : V → ℂ) := (Lp.stronglyMeasurable f).measurable
  set w : V → V := fun z => -((2 : ℝ) ^ k)⁻¹ • z with hw
  set G : V → V → ℂ := fun x z => (-1 : ℂ) ^ r * (fwdDiff (w z))^[r] (f : V → ℂ) x with hGdef
  have hG : Measurable (Function.uncurry G) := by
    have heq : Function.uncurry G = fun y : V × V => (-1 : ℂ) ^ r * ∑ l ∈ Finset.range (r + 1),
        ((-1 : ℂ) ^ (r - l) * (r.choose l : ℂ)) * (f : V → ℂ) (y.1 + (l : ℝ) • w y.2) := by
      funext y
      exact congrArg _ (higherDiff_apply r (w y.2) _ y.1)
    rw [heq]
    exact measurable_const.mul (Finset.measurable_sum _ fun l _ => measurable_const.mul
      (hfm.comp (measurable_fst.add ((measurable_snd.const_smul _).const_smul _))))
  have hω : lpModulus p r f k ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) eNorm_ne_top) (lpModulus_le r f k)
  -- the differences at the step `-2^(-k) z`
  have hbound : ∀ z, eLpNorm (fun x => G x z) p volume ≤
      ENNReal.ofReal (1 + ‖z‖) ^ r * lpModulus p r f k := fun z => by
    have hnorm : ‖w z‖ ≤ ‖z‖ * (1 / 2 ^ k) := by
      change ‖-((2 : ℝ) ^ k)⁻¹ • z‖ ≤ _
      rw [norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg (by positivity), one_div,
        mul_comm]
    have hD := aestronglyMeasurable_higherDiff (Lp.aestronglyMeasurable f) r (w z)
    calc eLpNorm (fun x => G x z) p volume
        = eLpNorm ((fwdDiff (w z))^[r] (f : V → ℂ)) p volume := by
          refine eLpNorm_congr_norm_ae ((hG.comp measurable_prodMk_right).aestronglyMeasurable)
            hD (Eventually.of_forall fun x => ?_)
          simp [G]
      _ ≤ modulus volume r p (f : V → ℂ) (‖z‖ * (1 / 2 ^ k)) :=
          eLpNorm_higherDiff_le_modulus hnorm
      _ ≤ ENNReal.ofReal (1 + ‖z‖) ^ r * modulus volume r p (f : V → ℂ) (1 / 2 ^ k) :=
          modulus_mul_le (Lp.aestronglyMeasurable f) hp1 r (norm_nonneg z) (by positivity)
  have hlhs : ‖f - jacksonApprox hp r k f‖ₑ =
      eLpNorm (fun x => ∫ z, lpKernel z * G x z) p volume := by
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae (ae_sub_jacksonApprox_eq hp r k f)
  rw [hlhs]
  exact eLpNorm_integral_lpKernel_mul_le hp1 hp r hG hω hbound

/-- **Jackson's inequality for the band-limited scheme**:
`E(f, E_k)_p ≤ C ω_r(f, 2^(-k))_p`. -/
theorem approxError_bandScheme_le (hp : p ≠ ∞) (r k : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    (bandScheme hp).approxError f (2 ^ k) ≤ jacksonConst V r p * lpModulus p r f k :=
  (ApproximationScheme.approxError_le_of_mem
    (mem_bandScheme_two_pow.2 (jacksonApprox_mem_bandSpace hp r k f)) f).trans
    (enorm_sub_jacksonApprox_le hp r k f)

end Rd

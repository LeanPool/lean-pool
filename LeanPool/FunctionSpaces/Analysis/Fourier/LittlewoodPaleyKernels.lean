/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Fourier.ApproxIdentity
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Littlewood–Paley kernels

On a finite-dimensional real inner product space `V` with Lebesgue measure, the Fourier transform
is `𝓕 f(ξ) = ∫ e^(-2πi⟪x, ξ⟫) f(x) dx` (Mathlib's `Real.fourier_eq`). For integrable `K`, the
transforms `𝓕K` and `𝓕⁻K` are continuous and bounded by `‖K‖_1`
(`Rd.continuous_fourier_of_integrable`, `Rd.norm_fourier_le_integral_norm`,
`Rd.enorm_fourier_le_lintegral`, `Rd.continuous_fourierInv_of_integrable`,
`Rd.norm_fourierInv_le_integral_norm`),
`𝓕K ∈ L_∞` (`Rd.memLp_top_fourier`), the transform respects sums and differences
(`Rd.fourier_add_apply`, `Rd.fourier_sub_apply`) and conjugation as `conj (𝓕 f) = 𝓕⁻(conj f)`,
`conj (𝓕⁻ f) = 𝓕(conj f)` for every `f : V → ℂ` (`Rd.conj_fourier_apply`,
`Rd.conj_fourierInv_apply`), `𝓕(K ⋆ L) = 𝓕K · 𝓕L` (`Rd.fourier_conv`),
`𝓕K(0) = ∫ K` (`Rd.fourier_apply_zero`), and the multiplication formula
`∫ 𝓕u · K = ∫ u · 𝓕K`, `∫ 𝓕⁻u · K = ∫ u · 𝓕⁻K` holds for integrable `u` and `K`
(`Rd.integral_fourier_mul`, `Rd.integral_fourierInv_mul`), in particular for Schwartz functions
`u` (`Rd.integral_fourier_smul_eq_of_integrable`, `Rd.integral_fourierInv_smul_eq_of_integrable`).
The character `t ↦ e^(2πit)` is `2π`-Lipschitz (`Rd.norm_fourierChar_sub_le`), so the inverse
transform of an integrable `g` vanishing outside the ball of radius `K` is Lipschitz with
constant `2πK ‖g‖_1` (`Rd.norm_fourierInv_sub_le`).
The kernels of the Littlewood–Paley decomposition are inverse transforms of smooth cut-offs:

* `Rd.cutoff a b`: a smooth function equal to `1` on the closed ball of radius `a` and to `0`
  outside the ball of radius `b` (Mathlib's `ContDiffBump`), a Schwartz function
  (`Rd.cutoffSchwartz`);
* `Rd.lpKernel = 𝓕⁻¹ χ_{1,2}` (`Rd.fourier_lpKernel`, `Rd.fourier_lpKernelS`) with
  `∫ lpKernel = 1` (`Rd.integral_lpKernel`), hence
  `1 ≤ ‖lpKernel‖_1 < ∞` (`Rd.one_le_eLpNorm_lpKernel`, `Rd.eLpNorm_lpKernel_ne_top`,
  `Rd.eLpNorm_lpKernel_lt_top`), and
  `Rd.bandKernel = 𝓕⁻¹ χ_{2,4}`;
* their dilations `Φ_k = Rd.Phi k` and `Θ_k = Rd.Theta k` by `2^k`, whose transforms are the
  cut-offs at scale `2^k` (`Rd.fourier_dilate`: `𝓕(Φ_c)(ξ) = 𝓕Φ(c^(-1) ξ)`), and the blocks
  `ψ_0 = Φ_0`, `ψ_j = Φ_j - Φ_{j-1}` (`Rd.psi`), with `∑_{j ≤ J} ψ_j = Φ_J` (`Rd.sum_psi`).

On the frequency side `𝓕Φ_k` lives in the ball of radius `2^(k+1)`, `𝓕Θ_k` in the ball of radius
`2^(k+2)` and equals `1` on the ball of radius `2^(k+1)`, and `𝓕ψ_{j+1}` lives in the annulus
`2^j ≤ |ξ| ≤ 2^(j+2)`. The transforms of the blocks satisfy `|𝓕ψ_j| ≤ 1`
(`Rd.norm_fourier_psi_le_one`, `Rd.enorm_fourier_psi_le_one`) and telescope,
`∑_{j ≤ J} 𝓕ψ_j = 𝓕Φ_J` (`Rd.sum_range_fourier_psi`); at every frequency `ξ` at most the two
blocks `a`, `a + 1` are nonzero, and their transforms add up to `1`
(`Rd.exists_fourier_psi_window`); and where `𝓕ψ_j(ξ) ≠ 0`, `4^j ≤ 4(1 + |ξ|²)`
(`Rd.four_pow_le_of_fourier_psi_ne_zero`). The **kernel identities** follow by comparing Fourier
transforms (`Rd.conv_eq_of_fourier`: if `𝓕K · 𝓕L = 𝓕M`, then `K ⋆ L = M`, by `Rd.fourier_conv`
and the inversion theorem `Continuous.fourierInv_fourier_eq`):

* `Θ_{k+1} ⋆ Θ_k = Θ_k` (`Rd.conv_Theta_succ`): the band-limited classes increase;
* `Θ_j ⋆ ψ_j = ψ_j` (`Rd.conv_Theta_psi`): the blocks are band-limited;
* `ψ_j ⋆ Θ_k = 0` for `j ≥ k + 3` (`Rd.conv_psi_Theta`): high blocks of band-limited functions
  vanish.
-/

@[expose] public section

open MeasureTheory Filter Topology Module ComplexConjugate
open scoped ENNReal FourierTransform SchwartzMap Real

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Dilations and the Fourier transform -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Dilations of continuous functions are continuous. -/
theorem continuous_dilate {Φ : V → ℂ} (hΦ : Continuous Φ) (c : ℝ) : Continuous (dilate c Φ) :=
  continuous_const.mul (hΦ.comp (continuous_const_smul c))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Dilations of bounded functions are bounded. -/
theorem bddAbove_dilate {Φ : V → ℂ} (hΦ : BddAbove (Set.range fun x => ‖Φ x‖)) (c : ℝ) :
    BddAbove (Set.range fun x => ‖dilate c Φ x‖) := by
  obtain ⟨B, hB⟩ := hΦ
  refine ⟨‖(((c ^ finrank ℝ V : ℝ)) : ℂ)‖ * B, Set.forall_mem_range.2 fun x => ?_⟩
  rw [dilate, norm_mul]
  exact mul_le_mul_of_nonneg_left (hB (Set.mem_range_self _)) (norm_nonneg _)

/-- **The dilation formula**: `𝓕(Φ_c)(ξ) = 𝓕Φ(c^(-1) ξ)` for `c > 0`, by the substitution
`y = c x` (Mathlib's `Measure.integral_comp_smul`). -/
theorem fourier_dilate (Φ : V → ℂ) {c : ℝ} (hc : 0 < c) (ξ : V) :
    𝓕 (dilate c Φ) ξ = 𝓕 Φ (c⁻¹ • ξ) := by
  have hpow : (0 : ℝ) < c ^ finrank ℝ V := pow_pos hc _
  have hinner : ∀ v : V, inner ℝ (c • v) (c⁻¹ • ξ) = inner ℝ v ξ := fun v => by
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hc.ne',
      one_mul]
  have h : ∀ v : V, 𝐞 (-inner ℝ v ξ) • dilate c Φ v = (((c ^ finrank ℝ V : ℝ)) : ℂ) *
      (fun y => 𝐞 (-inner ℝ y (c⁻¹ • ξ)) • Φ y) (c • v) := fun v => by
    simp only [dilate, hinner, Circle.smul_def, smul_eq_mul]
    ring
  rw [Real.fourier_eq, Real.fourier_eq]
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_smul volume
    (fun y => 𝐞 (-inner ℝ y (c⁻¹ • ξ)) • Φ y) c, abs_of_pos (inv_pos.2 hpow), Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpow.ne', Complex.ofReal_one, one_mul]

/-- The dilation formula read backwards: `𝓕Φ(ζ) = 𝓕(Φ_c)(c ζ)` for `c > 0`. -/
theorem fourier_eq_fourier_dilate (Φ : V → ℂ) {c : ℝ} (hc : 0 < c) (ζ : V) :
    𝓕 Φ ζ = 𝓕 (dilate c Φ) (c • ζ) := by
  rw [fourier_dilate _ hc, inv_smul_smul₀ hc.ne']

/-- The Fourier transform of a dilation is integrable if that of the function is. -/
theorem integrable_fourier_dilate {Φ : V → ℂ} (hΦ : Integrable (𝓕 Φ)) {c : ℝ} (hc : 0 < c) :
    Integrable (𝓕 (dilate c Φ)) := by
  rw [show 𝓕 (dilate c Φ) = fun ξ => 𝓕 Φ (c⁻¹ • ξ) from funext (fourier_dilate Φ hc)]
  exact hΦ.comp_smul (inv_ne_zero hc.ne')

/-! ### The Fourier transform of integrable functions -/

/-- The Fourier transform of a sum of integrable functions is the sum of the transforms (Mathlib's
`VectorFourier.fourierIntegral_add`). -/
theorem fourier_add_apply {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : V) :
    𝓕 (f + g) ξ = 𝓕 f ξ + 𝓕 g ξ :=
  congrFun (VectorFourier.fourierIntegral_add Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf hg) ξ

/-- The Fourier transform of a difference of integrable functions is the difference of the
transforms. -/
theorem fourier_sub_apply {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : V) :
    𝓕 (f - g) ξ = 𝓕 f ξ - 𝓕 g ξ := by
  simp only [Real.fourier_eq, Pi.sub_apply, smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff ξ).2 hf)
    ((Real.fourierIntegral_convergent_iff ξ).2 hg)

/-- **Conjugation and the Fourier transform**: for `f : V → ℂ` and `ξ ∈ V`,
`conj (𝓕 f(ξ)) = 𝓕⁻(conj ∘ f)(ξ)`, since `conj e^{-2πi⟨x, ξ⟩} = e^{2πi⟨x, ξ⟩}`. -/
theorem conj_fourier_apply (f : V → ℂ) (ξ : V) :
    conj (𝓕 f ξ) = 𝓕⁻ (fun x => conj (f x)) ξ := by
  rw [Real.fourier_eq, Real.fourierInv_eq, ← integral_conj]
  congr 1 with x
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul,
    Circle.starRingEnd_addChar, neg_neg]

/-- **Conjugation and the inverse Fourier transform**: for `f : V → ℂ` and `x ∈ V`,
`conj (𝓕⁻ f(x)) = 𝓕(conj ∘ f)(x)`. -/
theorem conj_fourierInv_apply (f : V → ℂ) (x : V) :
    conj (𝓕⁻ f x) = 𝓕 (fun ξ => conj (f ξ)) x := by
  rw [Real.fourierInv_eq, Real.fourier_eq, ← integral_conj]
  congr 1 with ξ
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul,
    Circle.starRingEnd_addChar]

/-- **The Fourier transform of a convolution** is the product of the transforms:
`𝓕(K ⋆ L)(ξ) = 𝓕K(ξ) 𝓕L(ξ)` for integrable `K` and `L` (Mathlib's
`Real.fourier_bilin_convolution_eq`). -/
theorem fourier_conv {K L : V → ℂ} (hK : Integrable K) (hL : Integrable L) (ξ : V) :
    𝓕 (conv K L volume) ξ = 𝓕 K ξ * 𝓕 L ξ := by
  rw [conv, Real.fourier_bilin_convolution_eq _ hK hL]
  rfl

/-- **The Fourier transform at the origin is the integral**: `𝓕K(0) = ∫ K`. -/
theorem fourier_apply_zero (K : V → ℂ) : 𝓕 K 0 = ∫ x, K x := by
  simp [Real.fourier_eq]

/-- **The Fourier transform of an integrable function is continuous** (Mathlib's
`VectorFourier.fourierIntegral_continuous`). -/
theorem continuous_fourier_of_integrable {K : V → ℂ} (hK : Integrable K) : Continuous (𝓕 K) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hK

/-- **The multiplication formula** `∫ 𝓕f · g = ∫ f · 𝓕g` for integrable `f, g : V → ℂ`: both
sides are the double integral `∫∫ e^(-2πi⟪x, ξ⟫) f(x) g(ξ) dx dξ` (Fubini, Mathlib's
`VectorFourier.integral_bilin_fourierIntegral_eq_flip` with the product as bilinear form). -/
theorem integral_fourier_mul {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ)
    (L := innerₗ V) Real.continuous_fourierChar continuous_inner hf hg

/-- **The multiplication formula for the inverse transform** `∫ 𝓕⁻f · g = ∫ f · 𝓕⁻g` for
integrable `f, g : V → ℂ` (the pairing `-⟪ξ, x⟫` in Mathlib's
`VectorFourier.integral_bilin_fourierIntegral_eq_flip`). -/
theorem integral_fourierInv_mul {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x := by
  have hL : (-innerₗ V).flip = -innerₗ V := by
    ext x y
    simp [real_inner_comm]
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ)
    (L := -innerₗ V) Real.continuous_fourierChar continuous_inner.neg hf hg
  rw [hL] at h
  simpa using! h

/-- **Duality for the Fourier transform** (the multiplication formula), `∫ 𝓕u · g = ∫ u · 𝓕g`,
for a Schwartz function `u` and an integrable function `g` (`Rd.integral_fourier_mul`). -/
theorem integral_fourier_smul_eq_of_integrable (u : 𝓢(V, ℂ)) {g : V → ℂ} (hg : Integrable g) :
    ∫ ξ, 𝓕 u ξ • g ξ = ∫ x, u x • 𝓕 g x := by
  simpa [SchwartzMap.fourier_coe] using integral_fourier_mul u.integrable hg

/-- The Fourier transform of a function is bounded by its `L_1` norm:
`|𝓕K(ξ)| ≤ ∫ |K|` for every `ξ` (Mathlib's `VectorFourier.norm_fourierIntegral_le_integral_norm`).
-/
theorem norm_fourier_le_integral_norm (K : V → ℂ) (ξ : V) : ‖𝓕 K ξ‖ ≤ ∫ x, ‖K x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ V) K ξ

/-- The Fourier transform of a function is bounded by its `L_1` norm, in `ℝ≥0∞`:
`|𝓕K(ξ)| ≤ ∫ |K|` for every `K` and `ξ` (Mathlib's `eNorm_integral_le_lintegral_eNorm`, with
`|e^(-2πi⟪x, ξ⟫)| = 1`). -/
theorem enorm_fourier_le_lintegral (K : V → ℂ) (ξ : V) : ‖𝓕 K ξ‖ₑ ≤ ∫⁻ x, ‖K x‖ₑ := by
  rw [Real.fourier_eq]
  simpa using eNorm_integral_le_lintegral_eNorm (fun v => 𝐞 (-inner ℝ v ξ) • K v)

/-- The Fourier transform of an integrable function lies in `L_∞`: it is continuous
(`Rd.continuous_fourier_of_integrable`) and bounded by `‖K‖_1`. -/
theorem memLp_top_fourier {K : V → ℂ} (hK : Integrable K) : MemLp (𝓕 K) ∞ volume :=
  memLp_top_of_bound (continuous_fourier_of_integrable hK).aestronglyMeasurable _
    (ae_of_all _ (norm_fourier_le_integral_norm K))

/-- The inverse Fourier transform `𝓕⁻g(x) = ∫ e^(2πi⟪ξ, x⟫) g(ξ) dξ` of an integrable function is
continuous, since `𝓕⁻g(x) = 𝓕g(-x)` (Mathlib's `Real.fourierInv_eq_fourier_neg`). -/
theorem continuous_fourierInv_of_integrable {g : V → ℂ} (hg : Integrable g) :
    Continuous (𝓕⁻ g) := by
  rw [show 𝓕⁻ g = fun x => 𝓕 g (-x) from funext (Real.fourierInv_eq_fourier_neg g)]
  exact (continuous_fourier_of_integrable hg).comp continuous_neg

/-- The inverse Fourier transform is bounded by the `L_1` norm: `|𝓕⁻g(x)| ≤ ∫ |g|` for every
`x`. -/
theorem norm_fourierInv_le_integral_norm (g : V → ℂ) (x : V) : ‖𝓕⁻ g x‖ ≤ ∫ ξ, ‖g ξ‖ := by
  rw [Real.fourierInv_eq_fourier_neg]
  exact norm_fourier_le_integral_norm g (-x)

/-- **Duality for the inverse Fourier transform** (the multiplication formula),
`∫ 𝓕⁻u · g = ∫ u · 𝓕⁻g`, for a Schwartz function `u` and an integrable function `g`
(`Rd.integral_fourierInv_mul`). -/
theorem integral_fourierInv_smul_eq_of_integrable (u : 𝓢(V, ℂ)) {g : V → ℂ}
    (hg : Integrable g) : ∫ ξ, 𝓕⁻ u ξ • g ξ = ∫ x, u x • 𝓕⁻ g x := by
  simpa [SchwartzMap.fourierInv_coe] using integral_fourierInv_mul u.integrable hg

/-- The character `t ↦ e^(2πit)` is `2π`-Lipschitz: `|e^(2πia) - e^(2πib)| ≤ 2π |a - b|`
(Mathlib's `Real.norm_exp_I_mul_ofReal_sub_one_le`). -/
theorem norm_fourierChar_sub_le (a b : ℝ) : ‖(𝐞 a : ℂ) - 𝐞 b‖ ≤ 2 * π * |a - b| := by
  have h : (𝐞 a : ℂ) - 𝐞 b = 𝐞 b * (𝐞 (a - b) - 1) := by
    rw [mul_sub, mul_one, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_sub_cancel]
  rw [h, norm_mul, Circle.norm_coe, one_mul, Real.fourierChar_apply, mul_comm _ Complex.I]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos Real.two_pi_pos]

/-- **Band-limited functions are Lipschitz**: if `g` is integrable and `g(ξ) = 0` for almost
every `ξ` with `|ξ| > K`, then `|𝓕⁻g(x) - 𝓕⁻g(y)| ≤ 2πK |x - y| ∫ |g|` for all `x, y`, since
`|e^(2πi⟪ξ, x⟫) - e^(2πi⟪ξ, y⟫)| ≤ 2π |⟪ξ, x - y⟫| ≤ 2πK |x - y|` for `|ξ| ≤ K`. -/
theorem norm_fourierInv_sub_le {g : V → ℂ} (hg : Integrable g) {K : ℝ}
    (hgK : ∀ᵐ ξ, K < ‖ξ‖ → g ξ = 0) (x y : V) :
    ‖𝓕⁻ g x - 𝓕⁻ g y‖ ≤ 2 * π * K * ‖x - y‖ * ∫ ξ, ‖g ξ‖ := by
  have hi : ∀ w : V, Integrable (fun ξ => 𝐞 (inner ℝ ξ w) • g ξ) := fun w => by
    simpa using (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (show Continuous fun p : V × V => (-innerₗ V) p.1 p.2 from continuous_inner.neg)
      (μ := volume) w).2 hg
  rw [Real.fourierInv_eq, Real.fourierInv_eq, ← integral_sub (hi x) (hi y),
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hg.norm.const_mul _) ?_
  filter_upwards [hgK] with ξ hξK
  simp only [Circle.smul_def, smul_eq_mul, ← sub_mul, norm_mul]
  by_cases hξ : K < ‖ξ‖
  · simp [hξK hξ]
  · push Not at hξ
    have h2 : |inner ℝ ξ x - inner ℝ ξ y| ≤ K * ‖x - y‖ := by
      rw [← inner_sub_right]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hξ (norm_nonneg _))
    gcongr
    calc _ ≤ 2 * π * |inner ℝ ξ x - inner ℝ ξ y| := norm_fourierChar_sub_le _ _
      _ ≤ 2 * π * (K * ‖x - y‖) := by gcongr
      _ = _ := by ring

/-! ### Smooth cut-offs -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Schwartz functions are bounded. -/
theorem bddAbove_schwartz [NormedSpace ℝ V] (f : 𝓢(V, ℂ)) :
    BddAbove (Set.range fun x => ‖f x‖) :=
  ⟨_, Set.forall_mem_range.2 fun x => SchwartzMap.norm_le_seminorm ℝ f x⟩

/-- The **smooth cut-off** `χ_{a,b}` with `0 < a < b`: `1` on the closed ball of radius `a`, `0`
outside the ball of radius `b`, with values in `[0, 1]` (Mathlib's `ContDiffBump`). -/
noncomputable def cutoff (a b : ℝ) (ha : 0 < a) (hab : a < b) (ξ : V) : ℂ :=
  (((⟨a, b, ha, hab⟩ : ContDiffBump (0 : V)) ξ : ℝ) : ℂ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off is `1` on the closed ball of radius `a`. -/
theorem cutoff_eq_one {a b : ℝ} (ha : 0 < a) (hab : a < b) {ξ : V} (hξ : ‖ξ‖ ≤ a) :
    cutoff a b ha hab ξ = 1 := by
  rw [cutoff, ContDiffBump.one_of_mem_closedBall _ (by simpa using hξ), Complex.ofReal_one]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off is `0` outside the ball of radius `b`. -/
theorem cutoff_eq_zero {a b : ℝ} (ha : 0 < a) (hab : a < b) {ξ : V} (hξ : b ≤ ‖ξ‖) :
    cutoff a b ha hab ξ = 0 := by
  rw [cutoff, ContDiffBump.zero_of_le_dist _ (by simpa using hξ), Complex.ofReal_zero]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Where the cut-off does not vanish, `‖ξ‖ < b`. -/
theorem norm_lt_of_cutoff_ne_zero {a b : ℝ} (ha : 0 < a) (hab : a < b) {ξ : V}
    (h : cutoff a b ha hab ξ ≠ 0) : ‖ξ‖ < b :=
  not_le.1 fun h' => h (cutoff_eq_zero ha hab h')

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off is smooth. -/
theorem contDiff_cutoff {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutoff (V := V) a b ha hab) :=
  Complex.ofRealCLM.contDiff.comp (ContDiffBump.contDiff _)

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off has compact support. -/
theorem hasCompactSupport_cutoff {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    HasCompactSupport (cutoff (V := V) a b ha hab) :=
  (ContDiffBump.hasCompactSupport _).comp_left Complex.ofReal_zero

/-- The cut-off as a **Schwartz function**. -/
noncomputable def cutoffSchwartz (a b : ℝ) (ha : 0 < a) (hab : a < b) : 𝓢(V, ℂ) :=
  (hasCompactSupport_cutoff ha hab).toSchwartzMap (contDiff_cutoff ha hab)

omit [MeasurableSpace V] [BorelSpace V] in
/-- The Schwartz cut-off is the cut-off. -/
theorem coe_cutoffSchwartz {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (cutoffSchwartz a b ha hab : V → ℂ) = cutoff a b ha hab :=
  rfl

/-! ### The kernels -/

/-- The **Littlewood–Paley kernel** `Φ = 𝓕⁻¹ χ_{1,2}`, a Schwartz function. -/
noncomputable def lpKernelS : 𝓢(V, ℂ) := 𝓕⁻ (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two)

/-- The **band-limiting kernel** `Θ = 𝓕⁻¹ χ_{2,4}`, a Schwartz function. -/
noncomputable def bandKernelS : 𝓢(V, ℂ) :=
  𝓕⁻ (cutoffSchwartz (V := V) 2 4 two_pos (by norm_num))

/-- The Littlewood–Paley kernel as a function. -/
noncomputable def lpKernel : V → ℂ := (lpKernelS : 𝓢(V, ℂ))

/-- The band-limiting kernel as a function. -/
noncomputable def bandKernel : V → ℂ := (bandKernelS : 𝓢(V, ℂ))

/-- `𝓕 Φ = χ_{1,2}`. -/
theorem fourier_lpKernel : 𝓕 (lpKernel (V := V)) = cutoff 1 2 one_pos one_lt_two := by
  rw [lpKernel, ← SchwartzMap.fourier_coe, lpKernelS, FourierInvPair.fourier_fourierInv_eq,
    coe_cutoffSchwartz]

/-- `𝓕 Φ = χ_{1,2}` as Schwartz functions (Mathlib's `FourierInvPair.fourier_fourierInv_eq`). -/
theorem fourier_lpKernelS :
    (𝓕 (lpKernelS (V := V)) : 𝓢(V, ℂ)) = cutoffSchwartz 1 2 one_pos one_lt_two :=
  FourierInvPair.fourier_fourierInv_eq _

/-- `𝓕 Θ = χ_{2,4}`. -/
theorem fourier_bandKernel : 𝓕 (bandKernel (V := V)) = cutoff 2 4 two_pos (by norm_num) := by
  rw [bandKernel, ← SchwartzMap.fourier_coe, bandKernelS, FourierInvPair.fourier_fourierInv_eq,
    coe_cutoffSchwartz]

/-- The Littlewood–Paley kernel is integrable. -/
theorem integrable_lpKernel : Integrable (lpKernel (V := V)) :=
  (lpKernelS : 𝓢(V, ℂ)).integrable

/-- The band-limiting kernel is integrable. -/
theorem integrable_bandKernel : Integrable (bandKernel (V := V)) :=
  (bandKernelS : 𝓢(V, ℂ)).integrable

/-- The Littlewood–Paley kernel is continuous. -/
theorem continuous_lpKernel : Continuous (lpKernel (V := V)) :=
  (lpKernelS : 𝓢(V, ℂ)).continuous

/-- The band-limiting kernel is continuous. -/
theorem continuous_bandKernel : Continuous (bandKernel (V := V)) :=
  (bandKernelS : 𝓢(V, ℂ)).continuous

/-- The Littlewood–Paley kernel is bounded. -/
theorem bddAbove_lpKernel : BddAbove (Set.range fun x => ‖lpKernel (V := V) x‖) :=
  bddAbove_schwartz _

/-- The band-limiting kernel is bounded. -/
theorem bddAbove_bandKernel : BddAbove (Set.range fun x => ‖bandKernel (V := V) x‖) :=
  bddAbove_schwartz _

/-- The Fourier transform of the Littlewood–Paley kernel is integrable. -/
theorem integrable_fourier_lpKernel : Integrable (𝓕 (lpKernel (V := V))) := by
  rw [fourier_lpKernel, ← coe_cutoffSchwartz]
  exact SchwartzMap.integrable _

/-- The Fourier transform of the band-limiting kernel is integrable. -/
theorem integrable_fourier_bandKernel : Integrable (𝓕 (bandKernel (V := V))) := by
  rw [fourier_bandKernel, ← coe_cutoffSchwartz]
  exact SchwartzMap.integrable _

/-- **The Littlewood–Paley kernel has integral `1`**: `∫ Φ = 𝓕Φ(0) = χ_{1,2}(0) = 1`. -/
theorem integral_lpKernel : ∫ x, lpKernel (V := V) x = 1 := by
  have h := congr_fun (fourier_lpKernel (V := V)) 0
  rw [Real.fourier_eq] at h
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul] at h
  rw [h]
  exact cutoff_eq_one _ _ (by simp)

/-! ### Dilated kernels and blocks -/

/-- The dilated Littlewood–Paley kernel `Φ_k = 2^(kn) Φ(2^k ·)`. -/
noncomputable def Phi (k : ℕ) : V → ℂ := dilate (2 ^ k) lpKernel

/-- The dilated band-limiting kernel `Θ_k = 2^(kn) Θ(2^k ·)`. -/
noncomputable def Theta (k : ℕ) : V → ℂ := dilate (2 ^ k) bandKernel

/-- The **Littlewood–Paley blocks** `ψ_0 = Φ_0`, `ψ_j = Φ_j - Φ_{j-1}`. -/
noncomputable def psi : ℕ → V → ℂ
  | 0 => Phi 0
  | j + 1 => Phi (j + 1) - Phi j

/-- **The blocks add up to the dilated kernel**: `∑_{j ≤ J} ψ_j = Φ_J`. -/
theorem sum_psi (J : ℕ) : ∑ j ∈ Finset.range (J + 1), psi (V := V) j = Phi J := by
  induction J with
  | zero => simp [psi]
  | succ J ih => rw [Finset.sum_range_succ, ih, psi, add_sub_cancel]

/-- The dilated kernels are integrable. -/
theorem integrable_Phi (k : ℕ) : Integrable (Phi (V := V) k) :=
  integrable_dilate integrable_lpKernel (by positivity)

/-- The dilated kernels are integrable. -/
theorem integrable_Theta (k : ℕ) : Integrable (Theta (V := V) k) :=
  integrable_dilate integrable_bandKernel (by positivity)

/-- The blocks are integrable. -/
theorem integrable_psi (j : ℕ) : Integrable (psi (V := V) j) := by
  cases j with
  | zero => exact integrable_Phi 0
  | succ j => exact (integrable_Phi (j + 1)).sub (integrable_Phi j)

/-- The dilated kernels are continuous. -/
theorem continuous_Phi (k : ℕ) : Continuous (Phi (V := V) k) :=
  continuous_dilate continuous_lpKernel _

/-- The dilated kernels are continuous. -/
theorem continuous_Theta (k : ℕ) : Continuous (Theta (V := V) k) :=
  continuous_dilate continuous_bandKernel _

/-- The blocks are continuous. -/
theorem continuous_psi (j : ℕ) : Continuous (psi (V := V) j) := by
  cases j with
  | zero => exact continuous_Phi 0
  | succ j => exact (continuous_Phi (j + 1)).sub (continuous_Phi j)

/-- The dilated kernels are bounded. -/
theorem bddAbove_Phi (k : ℕ) : BddAbove (Set.range fun x => ‖Phi (V := V) k x‖) :=
  bddAbove_dilate bddAbove_lpKernel _

/-- The dilated kernels are bounded. -/
theorem bddAbove_Theta (k : ℕ) : BddAbove (Set.range fun x => ‖Theta (V := V) k x‖) :=
  bddAbove_dilate bddAbove_bandKernel _

/-- The blocks are bounded. -/
theorem bddAbove_psi (j : ℕ) : BddAbove (Set.range fun x => ‖psi (V := V) j x‖) := by
  cases j with
  | zero => exact bddAbove_Phi 0
  | succ j =>
    obtain ⟨A, hA⟩ := bddAbove_Phi (V := V) (j + 1)
    obtain ⟨B, hB⟩ := bddAbove_Phi (V := V) j
    change BddAbove (Set.range fun x => ‖Phi (j + 1) x - Phi j x‖)
    exact ⟨A + B, Set.forall_mem_range.2 fun x => (norm_sub_le _ _).trans
      (add_le_add (hA (Set.mem_range_self x)) (hB (Set.mem_range_self x)))⟩

/-- `‖Φ_k‖_1 = ‖Φ‖_1`. -/
theorem eLpNorm_Phi_one (k : ℕ) :
    eLpNorm (Phi (V := V) k) 1 volume = eLpNorm (lpKernel (V := V)) 1 volume :=
  eLpNorm_dilate_one integrable_lpKernel (by positivity)

/-- `‖Θ_k‖_1 = ‖Θ‖_1`. -/
theorem eLpNorm_Theta_one (k : ℕ) :
    eLpNorm (Theta (V := V) k) 1 volume = eLpNorm (bandKernel (V := V)) 1 volume :=
  eLpNorm_dilate_one integrable_bandKernel (by positivity)

/-- The norm `‖Θ‖_1` of the band-limiting kernel is finite. -/
theorem eLpNorm_bandKernel_ne_top : eLpNorm (bandKernel (V := V)) 1 volume ≠ ⊤ :=
  (memLp_one_iff_integrable.2 integrable_bandKernel).eLpNorm_ne_top

/-- The norm `‖Φ‖_1` of the low-pass kernel is finite. -/
theorem eLpNorm_lpKernel_ne_top : eLpNorm (lpKernel (V := V)) 1 volume ≠ ⊤ :=
  (memLp_one_iff_integrable.2 integrable_lpKernel).eLpNorm_ne_top

/-- The norm `‖Φ‖_1` of the low-pass kernel is finite, as a strict inequality
(`Rd.eLpNorm_lpKernel_ne_top`). -/
theorem eLpNorm_lpKernel_lt_top : eLpNorm (lpKernel (V := V)) 1 volume < ⊤ :=
  eLpNorm_lpKernel_ne_top.lt_top

/-- **The kernel `Φ` has `L_1` norm at least `1`**: `‖Φ‖_1 ≥ |∫ Φ| = 1`
(`Rd.integral_lpKernel` and Mathlib's `eNorm_integral_le_lintegral_eNorm`). -/
theorem one_le_eLpNorm_lpKernel : 1 ≤ eLpNorm (lpKernel (V := V)) 1 volume :=
  calc (1 : ℝ≥0∞) = ‖∫ x, lpKernel (V := V) x‖ₑ := by rw [integral_lpKernel, eNorm_one]
    _ ≤ ∫⁻ x, ‖lpKernel (V := V) x‖ₑ := eNorm_integral_le_lintegral_eNorm _
    _ = eLpNorm (lpKernel (V := V)) 1 volume :=
        (eLpNorm_one_eq_lintegral_eNorm integrable_lpKernel.aestronglyMeasurable).symm

/-- `∫ |Θ_k| = ‖Θ‖_1` for every dilation, as a lower Lebesgue integral. -/
theorem lintegral_enorm_Theta (k : ℕ) :
    ∫⁻ y, ‖Theta (V := V) k y‖ₑ = eLpNorm (bandKernel (V := V)) 1 volume := by
  rw [← eLpNorm_one_eq_lintegral_eNorm (integrable_Theta k).aestronglyMeasurable,
    eLpNorm_Theta_one]

/-- `‖ψ_j‖_1 ≤ 2 ‖Φ‖_1`. -/
theorem eLpNorm_psi_one_le (j : ℕ) :
    eLpNorm (psi (V := V) j) 1 volume ≤ 2 * eLpNorm (lpKernel (V := V)) 1 volume := by
  cases j with
  | zero =>
    rw [two_mul]
    exact (eLpNorm_Phi_one 0).le.trans le_self_add
  | succ j =>
    change eLpNorm (Phi (j + 1) - Phi j) 1 volume ≤ _
    calc eLpNorm (Phi (V := V) (j + 1) - Phi j) 1 volume
        ≤ eLpNorm (Phi (V := V) (j + 1)) 1 volume + eLpNorm (Phi (V := V) j) 1 volume :=
          eLpNorm_sub_le le_rfl
      _ = 2 * eLpNorm (lpKernel (V := V)) 1 volume := by
          rw [eLpNorm_Phi_one, eLpNorm_Phi_one, two_mul]

/-- `∫ Φ_k = 1`. -/
theorem integral_Phi (k : ℕ) : ∫ x, Phi (V := V) k x = 1 := by
  rw [Phi, integral_dilate _ (by positivity), integral_lpKernel]

/-! ### The kernels on the frequency side -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `‖2^(-k) ξ‖ = ‖ξ‖ / 2^k`. -/
theorem norm_two_pow_inv_smul (k : ℕ) (ξ : V) : ‖((2 : ℝ) ^ k)⁻¹ • ξ‖ = ‖ξ‖ / 2 ^ k := by
  rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity), inv_mul_eq_div]

/-- `𝓕Φ_k(ξ) = χ_{1,2}(2^(-k) ξ)`. -/
theorem fourier_Phi (k : ℕ) (ξ : V) :
    𝓕 (Phi (V := V) k) ξ = cutoff 1 2 one_pos one_lt_two (((2 : ℝ) ^ k)⁻¹ • ξ) := by
  rw [Phi, fourier_dilate _ (by positivity), fourier_lpKernel]

/-- `𝓕Θ_k(ξ) = χ_{2,4}(2^(-k) ξ)`. -/
theorem fourier_Theta (k : ℕ) (ξ : V) :
    𝓕 (Theta (V := V) k) ξ = cutoff 2 4 two_pos (by norm_num) (((2 : ℝ) ^ k)⁻¹ • ξ) := by
  rw [Theta, fourier_dilate _ (by positivity), fourier_bandKernel]

/-- `𝓕ψ_{j+1} = 𝓕Φ_{j+1} - 𝓕Φ_j`. -/
theorem fourier_psi_succ (j : ℕ) (ξ : V) :
    𝓕 (psi (V := V) (j + 1)) ξ = 𝓕 (Phi (V := V) (j + 1)) ξ - 𝓕 (Phi (V := V) j) ξ :=
  fourier_sub_apply (integrable_Phi _) (integrable_Phi _) ξ

/-- The Fourier transforms of the dilated kernels are integrable. -/
theorem integrable_fourier_Phi (k : ℕ) : Integrable (𝓕 (Phi (V := V) k)) :=
  integrable_fourier_dilate integrable_fourier_lpKernel (by positivity)

/-- The Fourier transforms of the dilated kernels are integrable. -/
theorem integrable_fourier_Theta (k : ℕ) : Integrable (𝓕 (Theta (V := V) k)) :=
  integrable_fourier_dilate integrable_fourier_bandKernel (by positivity)

/-- The Fourier transforms of the blocks are integrable. -/
theorem integrable_fourier_psi (j : ℕ) : Integrable (𝓕 (psi (V := V) j)) := by
  cases j with
  | zero => exact integrable_fourier_Phi 0
  | succ j =>
    rw [show 𝓕 (psi (V := V) (j + 1)) = 𝓕 (Phi (V := V) (j + 1)) - 𝓕 (Phi (V := V) j) from
      funext (fourier_psi_succ j)]
    exact (integrable_fourier_Phi _).sub (integrable_fourier_Phi _)

/-- `𝓕Φ_k` vanishes outside the ball of radius `2^(k+1)`. -/
theorem norm_lt_of_fourier_Phi_ne_zero {k : ℕ} {ξ : V} (h : 𝓕 (Phi (V := V) k) ξ ≠ 0) :
    ‖ξ‖ < 2 ^ (k + 1) := by
  rw [fourier_Phi] at h
  have h1 := norm_lt_of_cutoff_ne_zero _ _ h
  rw [norm_two_pow_inv_smul, div_lt_iff₀ (by positivity)] at h1
  rw [pow_succ]
  linarith

/-- `𝓕Θ_k` vanishes outside the ball of radius `2^(k+2)`. -/
theorem norm_lt_of_fourier_Theta_ne_zero {k : ℕ} {ξ : V} (h : 𝓕 (Theta (V := V) k) ξ ≠ 0) :
    ‖ξ‖ < 2 ^ (k + 2) := by
  rw [fourier_Theta] at h
  have h1 := norm_lt_of_cutoff_ne_zero _ _ h
  rw [norm_two_pow_inv_smul, div_lt_iff₀ (by positivity)] at h1
  rw [pow_succ, pow_succ]
  linarith

/-- `𝓕Θ_k = 1` on the closed ball of radius `2^(k+1)`. -/
theorem fourier_Theta_eq_one {k : ℕ} {ξ : V} (h : ‖ξ‖ ≤ 2 ^ (k + 1)) :
    𝓕 (Theta (V := V) k) ξ = 1 := by
  rw [fourier_Theta]
  refine cutoff_eq_one _ _ ?_
  rw [norm_two_pow_inv_smul, div_le_iff₀ (by positivity)]
  rw [pow_succ] at h
  linarith

/-- `𝓕ψ_j` vanishes outside the ball of radius `2^(j+1)`. -/
theorem norm_lt_of_fourier_psi_ne_zero {j : ℕ} {ξ : V} (h : 𝓕 (psi (V := V) j) ξ ≠ 0) :
    ‖ξ‖ < 2 ^ (j + 1) := by
  cases j with
  | zero => exact norm_lt_of_fourier_Phi_ne_zero h
  | succ j =>
    rw [fourier_psi_succ] at h
    by_cases h1 : 𝓕 (Phi (V := V) (j + 1)) ξ = 0
    · rw [h1, zero_sub, neg_ne_zero] at h
      have h2 := norm_lt_of_fourier_Phi_ne_zero h
      rw [pow_succ (2 : ℝ) (j + 1)]
      linarith [pow_pos (two_pos : (0 : ℝ) < 2) (j + 1)]
    · exact norm_lt_of_fourier_Phi_ne_zero h1

/-- `𝓕ψ_{i+1}` vanishes on the closed ball of radius `2^i`. -/
theorem fourier_psi_succ_eq_zero {i : ℕ} {ξ : V} (h : ‖ξ‖ ≤ 2 ^ i) :
    𝓕 (psi (V := V) (i + 1)) ξ = 0 := by
  rw [fourier_psi_succ, fourier_Phi, fourier_Phi, cutoff_eq_one, cutoff_eq_one, sub_self]
  all_goals
    rw [norm_two_pow_inv_smul, div_le_iff₀ (by positivity), one_mul]
    first
      | exact h
      | exact h.trans (pow_le_pow_right₀ one_le_two (Nat.le_succ i))

/-- Where `𝓕ψ_{i+1}(ξ) ≠ 0`, `‖ξ‖ > 2^i`: the contrapositive of `Rd.fourier_psi_succ_eq_zero`. -/
theorem lt_norm_of_fourier_psi_succ_ne_zero {i : ℕ} {ξ : V}
    (h : 𝓕 (psi (V := V) (i + 1)) ξ ≠ 0) : 2 ^ i < ‖ξ‖ :=
  not_le.1 fun h' => h (fourier_psi_succ_eq_zero h')

/-- `𝓕Θ_{k+1} · 𝓕Θ_k = 𝓕Θ_k`. -/
theorem fourier_Theta_succ_mul (k : ℕ) (ξ : V) :
    𝓕 (Theta (V := V) (k + 1)) ξ * 𝓕 (Theta (V := V) k) ξ = 𝓕 (Theta (V := V) k) ξ := by
  by_cases h : 𝓕 (Theta (V := V) k) ξ = 0
  · rw [h, mul_zero]
  · rw [fourier_Theta_eq_one (k := k + 1) (norm_lt_of_fourier_Theta_ne_zero h).le, one_mul]

/-- `𝓕Θ_j · 𝓕ψ_j = 𝓕ψ_j`. -/
theorem fourier_Theta_mul_psi (j : ℕ) (ξ : V) :
    𝓕 (Theta (V := V) j) ξ * 𝓕 (psi (V := V) j) ξ = 𝓕 (psi (V := V) j) ξ := by
  by_cases h : 𝓕 (psi (V := V) j) ξ = 0
  · rw [h, mul_zero]
  · rw [fourier_Theta_eq_one (norm_lt_of_fourier_psi_ne_zero h).le, one_mul]

/-- `𝓕ψ_j · 𝓕Θ_k = 0` for `j ≥ k + 3`. -/
theorem fourier_psi_mul_Theta {j k : ℕ} (hjk : k + 3 ≤ j) (ξ : V) :
    𝓕 (psi (V := V) j) ξ * 𝓕 (Theta (V := V) k) ξ = 0 := by
  by_cases h : 𝓕 (Theta (V := V) k) ξ = 0
  · rw [h, mul_zero]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [fourier_psi_succ_eq_zero, zero_mul]
    exact (norm_lt_of_fourier_Theta_ne_zero h).le.trans
      (pow_le_pow_right₀ one_le_two (by omega))

/-- **The Fourier transforms of the blocks are bounded by `1`**: `|𝓕ψ_j(ξ)| ≤ 1`, since
`𝓕ψ_0 = χ(ξ)` and `𝓕ψ_{j+1} = χ(2^(-j-1) ξ) - χ(2^(-j) ξ)` with a cut-off `χ` with values in
`[0, 1]`. -/
theorem norm_fourier_psi_le_one (j : ℕ) (ξ : V) : ‖𝓕 (psi (V := V) j) ξ‖ ≤ 1 := by
  set b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h : ∀ x : V, cutoff 1 2 one_pos one_lt_two x = ((b x : ℝ) : ℂ) := fun x => rfl
  cases j with
  | zero =>
    rw [show psi (V := V) 0 = Phi 0 from rfl, fourier_Phi, h, Complex.norm_real,
      Real.norm_of_nonneg b.nonneg]
    exact b.le_one
  | succ j =>
    rw [fourier_psi_succ, fourier_Phi, fourier_Phi, h, h, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_sub_le_iff]
    constructor <;> linarith [b.nonneg' (((2 : ℝ) ^ (j + 1))⁻¹ • ξ),
      b.nonneg' (((2 : ℝ) ^ j)⁻¹ • ξ), b.le_one (x := ((2 : ℝ) ^ (j + 1))⁻¹ • ξ),
      b.le_one (x := ((2 : ℝ) ^ j)⁻¹ • ξ)]

/-- `|𝓕ψ_j(ξ)| ≤ 1` in `ℝ≥0∞`. -/
theorem enorm_fourier_psi_le_one (j : ℕ) (ξ : V) : ‖𝓕 (psi (V := V) j) ξ‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (norm_fourier_psi_le_one j ξ)

/-- **The Fourier transforms of the blocks telescope**:
`∑_{j ≤ J} 𝓕ψ_j(ξ) = 𝓕Φ_J(ξ)`. -/
theorem sum_range_fourier_psi (J : ℕ) (ξ : V) :
    ∑ j ∈ Finset.range (J + 1), 𝓕 (psi (V := V) j) ξ = 𝓕 (Phi (V := V) J) ξ := by
  induction J with
  | zero => simp [psi]
  | succ J ih => rw [Finset.sum_range_succ, ih, fourier_psi_succ]; ring

/-- **At most two blocks see a frequency**: for every `ξ ∈ V` there is `a ∈ ℕ` with
`‖ξ‖ < 2^(a+1)` such that `𝓕ψ_j(ξ) = 0` for `j ∉ {a, a+1}` and
`𝓕ψ_a(ξ) + 𝓕ψ_{a+1}(ξ) = 1`. Here `a` is the least index with `‖ξ‖ < 2^(a+1)`: the blocks below
`a` vanish at `ξ` since `𝓕ψ_j` lives on `‖ξ‖ < 2^(j+1)`, those above `a + 1` since `𝓕ψ_{i+1}`
vanishes on `‖ξ‖ ≤ 2^i`, and the sum of all blocks up to `a + 1` is `𝓕Φ_{a+1}(ξ) = 1`. -/
theorem exists_fourier_psi_window (ξ : V) : ∃ a : ℕ, ‖ξ‖ < 2 ^ (a + 1) ∧
    (∀ j, 𝓕 (psi (V := V) j) ξ ≠ 0 → j = a ∨ j = a + 1) ∧
    𝓕 (psi (V := V) a) ξ + 𝓕 (psi (V := V) (a + 1)) ξ = 1 := by
  classical
  have hex : ∃ a : ℕ, ‖ξ‖ < 2 ^ (a + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖ξ‖ (one_lt_two : (1 : ℝ) < 2)
    exact ⟨n, hn.trans (pow_lt_pow_right₀ one_lt_two n.lt_succ_self)⟩
  obtain ⟨a, ha, hmin⟩ : ∃ a : ℕ, ‖ξ‖ < 2 ^ (a + 1) ∧ ∀ j < a, ¬ ‖ξ‖ < 2 ^ (j + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hlow : ∀ j < a, 𝓕 (psi (V := V) j) ξ = 0 := fun j hj => by
    by_contra h
    exact hmin j hj (norm_lt_of_fourier_psi_ne_zero h)
  have hhigh : ∀ j, a + 1 < j → 𝓕 (psi (V := V) j) ξ = 0 := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact fourier_psi_succ_eq_zero (ha.le.trans (pow_le_pow_right₀ one_le_two (by omega)))
  refine ⟨a, ha, fun j hj => ?_, ?_⟩
  · by_contra hne
    push Not at hne
    rcases lt_or_gt_of_ne hne.1 with h | h
    · exact hj (hlow j h)
    · exact hj (hhigh j (by omega))
  · have hsum := sum_range_fourier_psi (V := V) (a + 1) ξ
    rw [fourier_Phi, cutoff_eq_one _ _ (by
      rw [norm_two_pow_inv_smul, div_le_one (by positivity)]; exact ha.le)] at hsum
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero
      (fun j hj => hlow j (Finset.mem_range.1 hj)), zero_add] at hsum
    exact hsum

/-- Where the block `ψ_j` sees the frequency `ξ`, its scale is at most that of `ξ`: if
`𝓕ψ_j(ξ) ≠ 0`, then `4^j ≤ 4(1 + ‖ξ‖²)` (for `j ≥ 1`, `‖ξ‖ > 2^(j-1)`). -/
theorem four_pow_le_of_fourier_psi_ne_zero {j : ℕ} {ξ : V} (h : 𝓕 (psi (V := V) j) ξ ≠ 0) :
    (4 : ℝ) ^ j ≤ 4 * (1 + ‖ξ‖ ^ 2) := by
  cases j with
  | zero => nlinarith [sq_nonneg ‖ξ‖]
  | succ i =>
    have hi : (2 : ℝ) ^ i < ‖ξ‖ := not_le.1 fun h' => h (fourier_psi_succ_eq_zero h')
    have h4 : (4 : ℝ) ^ (i + 1) = 4 * ((2 : ℝ) ^ i) ^ 2 := by
      rw [← pow_mul, pow_succ, mul_comm i 2, pow_mul]
      norm_num
      ring
    rw [h4]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) i]

/-! ### Kernel identities -/

/-- **Kernel identities from Fourier transforms**: if `K`, `L`, `M` are integrable, `L` is bounded
and continuous, `M` is continuous with integrable Fourier transform, and `𝓕K · 𝓕L = 𝓕M`, then
`K ⋆ L = M`. Both sides have the same transform (`Rd.fourier_conv`), and the inversion theorem
applies to continuous integrable functions with integrable transform
(`Continuous.fourierInv_fourier_eq`). -/
theorem conv_eq_of_fourier {K L M : V → ℂ} (hK : Integrable K) (hL : Integrable L)
    (hLc : Continuous L) (hLb : BddAbove (Set.range fun x => ‖L x‖)) (hM : Integrable M)
    (hMc : Continuous M) (hFM : Integrable (𝓕 M)) (h : ∀ ξ, 𝓕 K ξ * 𝓕 L ξ = 𝓕 M ξ) :
    conv K L volume = M := by
  have hKL : Integrable (conv K L volume) :=
    hK.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hL
  have hc : Continuous (conv K L volume) :=
    hLb.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ) hK hLc
  have hF : 𝓕 (conv K L volume) = 𝓕 M := funext fun ξ => (fourier_conv hK hL ξ).trans (h ξ)
  have hFKL : Integrable (𝓕 (conv K L volume)) := by
    rw [hF]
    exact hFM
  rw [← hc.fourierInv_fourier_eq hKL hFKL, hF, hMc.fourierInv_fourier_eq hM hFM]

/-- **The band-limited classes increase**: `Θ_{k+1} ⋆ Θ_k = Θ_k`. -/
theorem conv_Theta_succ (k : ℕ) :
    conv (Theta (V := V) (k + 1)) (Theta k) volume = Theta k :=
  conv_eq_of_fourier (integrable_Theta _) (integrable_Theta _) (continuous_Theta _)
    (bddAbove_Theta _) (integrable_Theta _) (continuous_Theta _) (integrable_fourier_Theta _)
    (fourier_Theta_succ_mul k)

/-- **The blocks are band-limited**: `Θ_j ⋆ ψ_j = ψ_j`. -/
theorem conv_Theta_psi (j : ℕ) : conv (Theta (V := V) j) (psi j) volume = psi j :=
  conv_eq_of_fourier (integrable_Theta _) (integrable_psi _) (continuous_psi _)
    (bddAbove_psi _) (integrable_psi _) (continuous_psi _) (integrable_fourier_psi _)
    (fourier_Theta_mul_psi j)

/-- **High blocks annihilate band-limited kernels**: `ψ_j ⋆ Θ_k = 0` for `j ≥ k + 3`. -/
theorem conv_psi_Theta {j k : ℕ} (hjk : k + 3 ≤ j) :
    conv (psi (V := V) j) (Theta k) volume = 0 := by
  have h0 : 𝓕 (0 : V → ℂ) = 0 := funext fun ξ => by simp [Real.fourier_eq]
  refine conv_eq_of_fourier (integrable_psi _) (integrable_Theta _) (continuous_Theta _)
    (bddAbove_Theta _) (integrable_zero _ _ _) continuous_zero ?_ fun ξ => ?_
  · rw [h0]
    exact integrable_zero _ _ _
  · rw [h0, fourier_psi_mul_Theta hjk]
    rfl

end Rd

/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.Lipschitz
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.Lattice
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.PSeries

/-!
# Smooth periodic functions on `ℝ^ι`, their Fourier series and Fourier multipliers

For `ℤ^ι`-periodic functions `g : ℝ^ι → ℂ` (`UnitAddTorus.IsPeriodic`), with the Fourier
coefficients `ĝ (n) = ∫_{(0,1)^ι} e^{−2πi ⟨n, x⟩} g (x) dx` (`UnitAddTorus.cubeFourierCoeff`) and
the monomials `e_n (x) = e^{2πi ⟨n, x⟩}` (`UnitAddTorus.mFourier n (UnitAddTorus.ofPi x)`); the
norm `‖n‖` of `n ∈ ℤ^ι` is the sup norm. The arguments are the standard ones of Grafakos,
*Classical Fourier Analysis*, Chapter 3, and Katznelson, *An Introduction to Harmonic Analysis*,
Chapter I.

* A `C¹` periodic map is Lipschitz (`UnitAddTorus.IsPeriodic.exists_lipschitzWith`: its derivative
  is periodic and continuous, hence bounded, and the mean value inequality).
* The coefficients of a derivative: `(∂_v g)^ (n) = 2πi ⟨n, v⟩ ĝ (n)` for `C¹` periodic `g`
  (`UnitAddTorus.cubeFourierCoeff_fderiv_of_contDiff`), by the difference quotient argument.
* Rapid decay: for smooth periodic `g`, `(1 + ‖n‖)^k |ĝ (n)|` is bounded and summable for every
  `k` (`UnitAddTorus.exists_norm_cubeFourierCoeff_le`, `UnitAddTorus.summable_cubeFourierCoeff`),
  by integrating by parts `k` times in one coordinate.
* The Fourier series of a smooth periodic `g` converges absolutely to `g`
  (`UnitAddTorus.hasSum_cubeFourierCoeff_mul_mFourier`, from Mathlib's
  `hasSum_mFourier_series_apply_of_summable`), hence the uniqueness of the coefficients
  (`UnitAddTorus.eq_of_cubeFourierCoeff_eq`).
* Fourier multipliers `T_m g = Σ_n m (n) ĝ (n) e_n` (`UnitAddTorus.periodicMultiplier`) with
  polynomially bounded symbols `m` (`UnitAddTorus.IsPolyBounded`): `T_m g` is smooth and periodic
  (`UnitAddTorus.contDiff_periodicMultiplier`, by the Weierstrass M-test for all derivatives),
  with coefficients `m ĝ` (`UnitAddTorus.cubeFourierCoeff_periodicMultiplier`, by termwise
  integration); `T_m T_{m'} = T_{m m'}`, `T_1 = id`, `T_m ∂_v = T_{2πi ⟨·, v⟩ m}`, linearity, and
  `T_m` on trigonometric polynomials, by comparing coefficients.
* On `ℝ² ≅ ℂ`: the Wirtinger derivatives `∂ = ½ (∂_x − i ∂_y)`, `∂_zbar = ½ (∂_x + i ∂_y)`
  (`UnitAddTorus.dzPi`, `UnitAddTorus.dzbarPi`), with the symbols `πi (conj ν)` and `πi ν`,
  `ν = n₀ + i n₁` (`HarmonicAnalysis.latticePoint`); the inverse of `∂_zbar` on mean-zero smooth
  periodic functions, the multiplier with symbol `(πi ν)⁻¹` off `0`
  (`UnitAddTorus.dzbarPi_periodicMultiplier_dzbarInvSymbol`, `UnitAddTorus.exists_dzbarPi_eq`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Complex
open scoped ComplexConjugate Real ContDiff

/-! As in `Mathlib.Analysis.Fourier.AddCircleMulti` (whose local instances these are), the measure
on `ℝ / ℤ` is the Haar measure of total mass one. -/
attribute [local instance] instMeasureSpaceUnitAddCircle instIsAddHaarMeasureUnitAddCircleVolume
  instIsProbabilityMeasureUnitAddCircleVolume

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-! ### Periodic functions -/

omit [Fintype ι] in
/-- A continuous periodic function induces a continuous function on the torus. -/
theorem IsPeriodic.continuous_comp_toPi {E : Type*} [TopologicalSpace E] {g : (ι → ℝ) → E}
    (hc : Continuous g) (hper : IsPeriodic g) : Continuous (g ∘ toPi) := by
  have h1 : IsOpenQuotientMap (ofPi : (ι → ℝ) → UnitAddTorus ι) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  rw [← h1.continuous_comp_iff]
  convert hc using 1
  funext x
  exact hper.comp_toPi_ofPi x

omit [Fintype ι] in
/-- A continuous periodic function is bounded. -/
theorem IsPeriodic.exists_bound {E : Type*} [SeminormedAddCommGroup E] {g : (ι → ℝ) → E}
    (hc : Continuous g) (hper : IsPeriodic g) : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (hper.continuous_comp_toPi hc).continuousOn
  exact ⟨C, fun x => by simpa [hper.comp_toPi_ofPi x] using hC (ofPi x) (mem_univ _)⟩

omit [Fintype ι] in
/-- The derivative of a periodic map is periodic. -/
theorem isPeriodic_fderiv [Finite ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (ι → ℝ) → E} (hper : IsPeriodic g) : IsPeriodic (fderiv ℝ g) := by
  have := Fintype.ofFinite ι
  intro x k
  rw [← fderiv_comp_add_right]
  congr 1
  funext y
  exact hper y k

omit [Fintype ι] in
/-- The directional derivatives of a periodic map are periodic. -/
theorem IsPeriodic.fderiv_apply [Finite ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (ι → ℝ) → E} (hper : IsPeriodic g) (v : ι → ℝ) : IsPeriodic fun x => fderiv ℝ g x v :=
  fun x k => by simp only [isPeriodic_fderiv hper x k]

/-- A `C¹` periodic map is Lipschitz: its derivative is continuous and periodic, hence bounded,
and the mean value inequality applies. -/
theorem IsPeriodic.exists_lipschitzWith {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (ι → ℝ) → E} (hg : ContDiff ℝ 1 g) (hper : IsPeriodic g) :
    ∃ K : NNReal, LipschitzWith K g := by
  obtain ⟨C, hC⟩ := (isPeriodic_fderiv hper).exists_bound (hg.continuous_fderiv one_ne_zero)
  refine ⟨C.toNNReal, lipschitzWith_of_nnNorm_fderiv_le (hg.differentiable one_ne_zero)
    fun x => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnNorm]
  exact (hC x).trans (Real.le_coe_toNNReal C)

/-! ### Coefficients -/

/-- The coefficients are bounded by the sup norm. -/
theorem norm_cubeFourierCoeff_le {g : (ι → ℝ) → ℂ} {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (n : ι → ℤ) :
    ‖cubeFourierCoeff g n‖ ≤ C := by
  rw [cubeFourierCoeff]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cube ι)
    (f := fun x => mFourier (-n) (ofPi x) * g x) (C := C)
    (by rw [volume_cube]; exact ENNReal.one_lt_top)
    (fun x _ => by rw [norm_mul, norm_mFourier_ofPi, one_mul]; exact hC x)
  simpa [measureReal_def, volume_cube] using h

/-- The coefficients over the cube of a periodic `g` are the Fourier coefficients on the torus of
the function `g ∘ toPi` that `g` induces there. -/
theorem mFourierCoeff_comp_toPi {g : (ι → ℝ) → ℂ} (hper : IsPeriodic g) (n : ι → ℤ) :
    mFourierCoeff (g ∘ toPi) n = cubeFourierCoeff g n := by
  rw [mFourierCoeff, cubeFourierCoeff, ← integral_cube_ofPi]
  refine setIntegral_congr_fun measurableSet_cube fun x _ => ?_
  simp only [Function.comp_apply, hper.comp_toPi_ofPi, smul_eq_mul]

/-- The coefficients of the derivative of a Lipschitz `ℤ^ι`-periodic `g : ℝ^ι → ℂ`:
`(∂_v g)^ (n) = 2πi ⟨n, v⟩ ĝ (n)`, with `∂_v g (x) = fderiv ℝ g x v` (the derivative almost
everywhere, by Rademacher's theorem). The difference quotient argument of
`UnitAddTorus.cubeFourierCoeff_fderiv`: integrate `t⁻¹ (g (x + t v) − g (x))` against `e_{−n}`,
move the translation onto `e_{−n}` and let `t → 0`. -/
theorem cubeFourierCoeff_fderiv_of_lipschitzWith {g : (ι → ℝ) → ℂ} {C : NNReal}
    (hg : LipschitzWith C g) (hper : IsPeriodic g) (v : ι → ℝ) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => fderiv ℝ g x v) n =
      2 * π * I * (∑ i, (n i : ℂ) * (v i : ℂ)) * cubeFourierCoeff g n := by
  set A : ℝ → ℂ := fun t => ∫ x in cube ι,
    mFourier (-n) (ofPi x) * ((t⁻¹ : ℂ) * (g (x + t • v) - g x)) with hA
  -- the difference quotients converge to the derivative
  have h1 : Tendsto A (𝓝[≠] 0) (𝓝 (cubeFourierCoeff (fun x => fderiv ℝ g x v) n)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (C : ℝ) * ‖v‖) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t => ((continuous_mFourier_ofPi _).mul
        (continuous_const.mul ((hg.continuous.comp (continuous_id.add continuous_const)).sub
          hg.continuous))).aestronglyMeasurable
    · refine Eventually.of_forall fun t => ae_of_all _ fun x => ?_
      rw [norm_mul, norm_mFourier_ofPi, one_mul, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs]
      have h := hg.dist_le_mul (x + t • v) x
      rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
      by_cases ht : t = 0
      · simp only [ht, abs_zero, inv_zero, zero_mul]; positivity
      · have ht' : 0 < |t| := abs_pos.mpr ht
        calc |t|⁻¹ * ‖g (x + t • v) - g x‖ ≤ |t|⁻¹ * (C * (|t| * ‖v‖)) := by gcongr
          _ = C * ‖v‖ := by field_simp
    · exact integrableOn_const (by rw [volume_cube]; exact ENNReal.one_ne_top)
    · filter_upwards [ae_restrict_of_ae hg.ae_differentiableAt] with x hx
      have h0 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      have hd : HasDerivAt (fun t : ℝ => g (x + t • v)) (fderiv ℝ g x v) 0 :=
        hx.hasFDerivAt.comp_hasDerivAt_of_eq 0 h0 (by simp)
      have h2 := hasDerivAt_iff_tendsto_slope_zero.mp hd
      simp only [zero_add, zero_smul, add_zero] at h2
      refine (h2.const_mul (mFourier (-n) (ofPi x))).congr fun t => ?_
      rw [Complex.real_smul, Complex.ofReal_inv]
  -- the translation moves onto `e_{−n}`
  have h2 : ∀ t : ℝ, A t = (t⁻¹ : ℂ) * (mFourier n (ofPi (t • v)) - 1) * cubeFourierCoeff g n := by
    intro t
    have hcont : ∀ w : ι → ℝ, Continuous fun x => mFourier (-n) (ofPi x) * g (x + w) :=
      fun w => (continuous_mFourier_ofPi _).mul
        (hg.continuous.comp (continuous_id.add continuous_const))
    have e1 : ∀ x, mFourier (-n) (ofPi x) * ((t⁻¹ : ℂ) * (g (x + t • v) - g x)) =
        (t⁻¹ : ℂ) * (mFourier (-n) (ofPi x) * g (x + t • v) -
          mFourier (-n) (ofPi x) * g (x + 0)) := fun x => by
      rw [add_zero]; ring
    have hF : IsPeriodic fun y => mFourier (-n) (ofPi (y + -(t • v))) * g y := by
      intro y k
      simp only
      rw [show y + (fun i => (k i : ℝ)) + -(t • v) = (y + -(t • v)) + fun i => (k i : ℝ) by
        abel, ofPi_add_int, hper]
    have e2 : ∫ x in cube ι, mFourier (-n) (ofPi x) * g (x + t • v) =
        mFourier n (ofPi (t • v)) * cubeFourierCoeff g n := by
      have := integral_cube_comp_add hF (t • v)
      simp only [add_neg_cancel_right] at this
      rw [this, cubeFourierCoeff, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_cube fun y _ => ?_
      rw [mFourier_ofPi_add, mFourier_ofPi_neg n (-(t • v)), neg_neg]
      ring
    simp only [hA]
    simp_rw [e1]
    rw [integral_const_mul, integral_sub (integrableOn_cube_of_continuous (hcont _))
      (integrableOn_cube_of_continuous (hcont 0)), e2]
    simp only [add_zero, cubeFourierCoeff]
    ring
  have h3 := (tendsto_slope_mFourier_ofPi_smul n v).mul_const (cubeFourierCoeff g n)
  exact tendsto_nhds_unique h1 (h3.congr fun t => (h2 t).symm)

/-- The coefficients of the derivative of a `C¹` periodic `g : ℝ^ι → ℂ`:
`(∂_v g)^ (n) = 2πi ⟨n, v⟩ ĝ (n)`. -/
theorem cubeFourierCoeff_fderiv_of_contDiff {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) (v : ι → ℝ) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => fderiv ℝ g x v) n =
      2 * π * I * (∑ i, (n i : ℂ) * (v i : ℂ)) * cubeFourierCoeff g n := by
  obtain ⟨K, hK⟩ := hper.exists_lipschitzWith hg
  exact cubeFourierCoeff_fderiv_of_lipschitzWith hK hper v n

/-- The derivative of a `C¹` periodic function has mean zero. -/
theorem cubeFourierCoeff_fderiv_zero {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) (v : ι → ℝ) : cubeFourierCoeff (fun x => fderiv ℝ g x v) 0 = 0 := by
  rw [cubeFourierCoeff_fderiv_of_contDiff hg hper]
  simp

/-! ### Rapid decay and the Fourier series of a smooth periodic function -/

/-- The directional derivatives of a smooth map are smooth. -/
private lemma contDiff_fderiv_apply {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (v : ι → ℝ) :
    ContDiff ℝ ∞ fun x => fderiv ℝ g x v :=
  (contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const

private lemma contDiff_one_of_infty {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ 1 g :=
  hg.of_le (by exact_mod_cast le_top)

section Partial

variable [DecidableEq ι]

/-- The `j`-th iterate of the partial derivative `∂_i = fderiv ℝ · · (Pi.single i 1)`. -/
private def iterPartial (i : ι) (j : ℕ) (g : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  (fun f x => fderiv ℝ f x (Pi.single i 1))^[j] g

private lemma sum_mul_single (n : ι → ℤ) (i : ι) :
    ∑ l, (n l : ℂ) * ((Pi.single i (1 : ℝ) : ι → ℝ) l : ℂ) = n i := by
  rw [Finset.sum_eq_single i (fun l _ hl => by simp [Pi.single_eq_of_ne hl]) (by simp)]
  simp

/-- `∂_i^j g` is smooth and periodic, with coefficients `(2πi n_i)^j ĝ (n)`. -/
private lemma iterPartial_spec {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g)
    (i : ι) (j : ℕ) :
    ContDiff ℝ ∞ (iterPartial i j g) ∧ IsPeriodic (iterPartial i j g) ∧
      ∀ n, cubeFourierCoeff (iterPartial i j g) n =
        (2 * π * I * (n i : ℂ)) ^ j * cubeFourierCoeff g n := by
  induction j with
  | zero => exact ⟨hg, hper, fun n => by simp [iterPartial]⟩
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have e : iterPartial i (j + 1) g =
        fun x => fderiv ℝ (iterPartial i j g) x (Pi.single i 1) := by
      simp only [iterPartial, Function.iterate_succ_apply']
    rw [e]
    refine ⟨contDiff_fderiv_apply h1 _, h2.fderiv_apply _, fun n => ?_⟩
    rw [cubeFourierCoeff_fderiv_of_contDiff (contDiff_one_of_infty h1) h2, h3, pow_succ,
      sum_mul_single]
    ring

end Partial

/-- The sup norm of `n ∈ ℤ^ι` is the absolute value of one of its coordinates. -/
private lemma exists_norm_eq [Nonempty ι] (n : ι → ℤ) : ∃ i, ‖n‖ = ‖n i‖ := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun b => ‖n b‖₊
  exact ⟨i, by rw [Pi.norm_def, hi, coe_nnNorm]⟩

private lemma one_add_pow_le {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (1 + a) ^ k ≤ 2 ^ k * (1 + a ^ k) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ ≤ 2 ^ k * (1 + a ^ k) :=
        le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ha k])
  · calc (1 + a) ^ k ≤ (2 * a) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * a ^ k := mul_pow 2 a k
      _ ≤ 2 ^ k * (1 + a ^ k) := by gcongr; linarith

/-- Rapid decay of the coefficients of a smooth periodic `g`: `(1 + ‖n‖)^k |ĝ (n)|` is bounded,
by integrating by parts `k` times in one coordinate (the derivative formula
`UnitAddTorus.cubeFourierCoeff_fderiv_of_contDiff` along a coordinate vector). -/
theorem exists_norm_cubeFourierCoeff_le {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hper : IsPeriodic g) (k : ℕ) :
    ∃ C : ℝ, ∀ n : ι → ℤ, (1 + ‖n‖) ^ k * ‖cubeFourierCoeff g n‖ ≤ C := by
  classical
  -- `|n_i|^k |ĝ (n)| ≤ (2π |n_i|)^k |ĝ (n)| = |(∂_i^k g)^ (n)| ≤ sup |∂_i^k g|`
  have hb : ∀ i : ι, ∃ C : ℝ, ∀ n : ι → ℤ, ‖n i‖ ^ k * ‖cubeFourierCoeff g n‖ ≤ C := by
    intro i
    obtain ⟨h1, h2, h3⟩ := iterPartial_spec hg hper i k
    obtain ⟨C, hC⟩ := h2.exists_bound h1.continuous
    refine ⟨C, fun n => le_trans ?_ (norm_cubeFourierCoeff_le hC n)⟩
    rw [h3 n, norm_mul, norm_pow]
    gcongr
    rw [norm_mul, Complex.norm_intCast, ← Int.norm_eq_abs]
    refine le_mul_of_one_le_left (norm_nonneg _) ?_
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    nlinarith [Real.two_le_pi]
  choose C hC using hb
  obtain ⟨B, hB⟩ := hper.exists_bound hg.continuous
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hC0 : ∀ i, 0 ≤ C i := fun i => (by positivity : (0 : ℝ) ≤ _).trans (hC i 0)
  refine ⟨2 ^ k * (B + ∑ i, C i), fun n => ?_⟩
  have hB' := norm_cubeFourierCoeff_le hB n
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : ‖n‖ = 0 := by rw [Subsingleton.elim n 0, norm_zero]
    rw [this, add_zero, one_pow, one_mul, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact hB'.trans (le_mul_of_one_le_left hB0 (one_le_pow₀ one_le_two))
  · obtain ⟨i, hi⟩ := exists_norm_eq n
    rw [hi]
    calc (1 + ‖n i‖) ^ k * ‖cubeFourierCoeff g n‖
        ≤ 2 ^ k * (1 + ‖n i‖ ^ k) * ‖cubeFourierCoeff g n‖ := by
          gcongr; exact one_add_pow_le (norm_nonneg _) k
      _ = 2 ^ k * (‖cubeFourierCoeff g n‖ + ‖n i‖ ^ k * ‖cubeFourierCoeff g n‖) := by ring
      _ ≤ 2 ^ k * (B + C i) := by gcongr; exact hC i n
      _ ≤ 2 ^ k * (B + ∑ j, C j) := by
          gcongr; exact Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i)

/-- `Σ_{n ∈ ℤ^ι} (1 + ‖n‖)^{−2 card ι}` converges, by comparison with
`Π_i Σ_{m ∈ ℤ} (1 + |m|)^{−2}`. -/
theorem summable_one_add_norm_pow_inv :
    Summable fun n : ι → ℤ => ((1 + ‖n‖) ^ (2 * Fintype.card ι))⁻¹ := by
  classical
  set f : ℤ → ℝ := fun m => ((1 + ‖m‖) ^ 2)⁻¹ with hf_def
  have hf0 : ∀ m, 0 ≤ f m := fun m => by positivity
  have hf : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun m => ?_)
      ((Real.summable_one_div_int_pow.mpr one_lt_two).add (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable)
    by_cases hm : m = 0
    · simp [hf_def, hm]
    · have h1 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
      have h2 : (m : ℝ) ^ 2 ≤ (1 + ‖m‖) ^ 2 := by
        rw [Int.norm_eq_abs, ← sq_abs (m : ℝ)]
        gcongr
        linarith
      simp only [hf_def, hm, ↓reduceIte, add_zero, one_div]
      exact inv_anti₀ h1 h2
  have hprod : Summable fun n : ι → ℤ => ∏ i, f (n i) := by
    refine summable_of_sum_le (c := (∑' m, f m) ^ Fintype.card ι)
      (fun n => Finset.prod_nonneg fun i _ => hf0 _) fun S => ?_
    set T : Finset ℤ := S.biUnion fun n => Finset.univ.image n
    calc ∑ n ∈ S, ∏ i, f (n i) ≤ ∑ n ∈ Fintype.piFinset fun _ => T, ∏ i, f (n i) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun n hn => Fintype.mem_piFinset.2 fun i => Finset.mem_biUnion.2
              ⟨n, hn, Finset.mem_image_of_mem n (Finset.mem_univ i)⟩)
            (fun _ _ _ => Finset.prod_nonneg fun i _ => hf0 _)
      _ = ∏ _i : ι, ∑ m ∈ T, f m := (Finset.prod_univ_sum (fun _ => T) fun _ => f).symm
      _ ≤ ∏ _i : ι, ∑' m, f m :=
          Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun _ _ => hf0 _)
            fun _ _ => hf.sum_le_tsum T fun _ _ => hf0 _
      _ = (∑' m, f m) ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
  refine hprod.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have h : ∏ i, (1 + ‖n i‖) ^ 2 ≤ (1 + ‖n‖) ^ (2 * Fintype.card ι) := by
    rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
      fun i _ => pow_le_pow_left₀ (by positivity) (by linarith [norm_le_pi_norm n i]) 2
  simp only [hf_def, Finset.prod_inv_distrib]
  exact inv_anti₀ (Finset.prod_pos fun _ _ => by positivity) h

/-- For smooth periodic `g`, `Σ_n (1 + ‖n‖)^k |ĝ (n)|` converges for every `k`. -/
theorem summable_cubeFourierCoeff {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hper : IsPeriodic g) (k : ℕ) :
    Summable fun n : ι → ℤ => (1 + ‖n‖) ^ k * ‖cubeFourierCoeff g n‖ := by
  obtain ⟨C, hC⟩ := exists_norm_cubeFourierCoeff_le hg hper (k + 2 * Fintype.card ι)
  refine ((summable_one_add_norm_pow_inv (ι := ι)).mul_left C).of_nonneg_of_le
    (fun n => by positivity) fun n => ?_
  have hpos : 0 < (1 + ‖n‖) ^ (2 * Fintype.card ι) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc (1 + ‖n‖) ^ k * ‖cubeFourierCoeff g n‖ * (1 + ‖n‖) ^ (2 * Fintype.card ι)
      = (1 + ‖n‖) ^ (k + 2 * Fintype.card ι) * ‖cubeFourierCoeff g n‖ := by ring
    _ ≤ C := hC n

/-- The Fourier series of a smooth periodic `g` converges absolutely to `g`:
`g (x) = Σ_n ĝ (n) e^{2πi ⟨n, x⟩}` (Mathlib's `hasSum_mFourier_series_apply_of_summable` for the
function `g ∘ toPi` on the torus). -/
theorem hasSum_cubeFourierCoeff_mul_mFourier {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hper : IsPeriodic g) (x : ι → ℝ) :
    HasSum (fun n => cubeFourierCoeff g n * mFourier n (ofPi x)) (g x) := by
  set G : C(UnitAddTorus ι, ℂ) := ⟨g ∘ toPi, hper.continuous_comp_toPi hg.continuous⟩
  have hG : mFourierCoeff G = cubeFourierCoeff g := funext fun n => mFourierCoeff_comp_toPi hper n
  have hs : Summable (mFourierCoeff G) := by
    rw [hG]
    exact Summable.of_norm (by simpa using summable_cubeFourierCoeff hg hper 0)
  have := hasSum_mFourier_series_apply_of_summable hs (ofPi x)
  rw [hG] at this
  simpa [G, hper.comp_toPi_ofPi] using this

/-- Uniqueness of Fourier coefficients: smooth periodic functions with the same coefficients are
equal. -/
theorem eq_of_cubeFourierCoeff_eq {g g' : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hper : IsPeriodic g) (hg' : ContDiff ℝ ∞ g') (hper' : IsPeriodic g')
    (h : ∀ n, cubeFourierCoeff g n = cubeFourierCoeff g' n) : g = g' := by
  funext x
  have h1 := hasSum_cubeFourierCoeff_mul_mFourier hg hper x
  have h2 := hasSum_cubeFourierCoeff_mul_mFourier hg' hper' x
  simp_rw [← h] at h2
  exact h1.unique h2

/-- The coefficients of an absolutely convergent trigonometric series `Σ_l c_l e_l` are `c`
(termwise integration and the orthogonality of the monomials). -/
theorem cubeFourierCoeff_tsum_mFourier {c : (ι → ℤ) → ℂ} (hc : Summable c) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => ∑' l, c l * mFourier l (ofPi x)) n = c n := by
  have hint : ∀ l, Integrable (fun x => mFourier (-n) (ofPi x) * (c l * mFourier l (ofPi x)))
      (volume.restrict (cube ι)) := fun l =>
    integrableOn_cube_of_continuous ((continuous_mFourier_ofPi _).mul
      (continuous_const.mul (continuous_mFourier_ofPi _)))
  have hnorm : ∀ l, ∫ x in cube ι, ‖mFourier (-n) (ofPi x) * (c l * mFourier l (ofPi x))‖ =
      ‖c l‖ := fun l => by
    simp_rw [norm_mul, norm_mFourier_ofPi, one_mul, mul_one]
    simp [measureReal_def, volume_cube]
  have key := integral_tsum_of_summable_integral_norm hint (by simp_rw [hnorm]; exact hc.norm)
  have hl : ∀ l, ∫ x in cube ι, mFourier (-n) (ofPi x) * (c l * mFourier l (ofPi x)) =
      if l = n then c l else 0 := fun l => by
    have := cubeFourierCoeff_trig {l} c n
    simp only [Finset.sum_singleton, Finset.mem_singleton] at this
    rw [cubeFourierCoeff] at this
    rw [this]
    by_cases h : l = n
    · simp [h]
    · simp [h, Ne.symm h]
  rw [cubeFourierCoeff]
  simp_rw [← tsum_mul_left]
  rw [← key]
  simp_rw [hl]
  exact tsum_ite_eq n c

/-! ### Polynomially bounded symbols -/

/-- The symbol `m : ℤ^ι → ℂ` is polynomially bounded: `|m (n)| ≤ C (1 + ‖n‖)^k`. -/
def IsPolyBounded (m : (ι → ℤ) → ℂ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n, ‖m n‖ ≤ C * (1 + ‖n‖) ^ k

/-- Bounded symbols are polynomially bounded. -/
theorem isPolyBounded_of_norm_le {m : (ι → ℤ) → ℂ} {C : ℝ} (h : ∀ n, ‖m n‖ ≤ C) :
    IsPolyBounded m :=
  ⟨C, 0, fun n => by simpa using h n⟩

theorem isPolyBounded_const (c : ℂ) : IsPolyBounded fun _ : ι → ℤ => c :=
  isPolyBounded_of_norm_le fun _ => le_rfl

theorem IsPolyBounded.add {m m' : (ι → ℤ) → ℂ} (hm : IsPolyBounded m) (hm' : IsPolyBounded m') :
    IsPolyBounded fun n => m n + m' n := by
  obtain ⟨C, k, hC⟩ := hm
  obtain ⟨C', k', hC'⟩ := hm'
  refine ⟨|C| + |C'|, k + k', fun n => ?_⟩
  have h1 : 1 ≤ 1 + ‖n‖ := by linarith [norm_nonneg n]
  have hk : (1 + ‖n‖) ^ k ≤ (1 + ‖n‖) ^ (k + k') := pow_le_pow_right₀ h1 (by omega)
  have hk' : (1 + ‖n‖) ^ k' ≤ (1 + ‖n‖) ^ (k + k') := pow_le_pow_right₀ h1 (by omega)
  calc ‖m n + m' n‖ ≤ ‖m n‖ + ‖m' n‖ := norm_add_le _ _
    _ ≤ C * (1 + ‖n‖) ^ k + C' * (1 + ‖n‖) ^ k' := add_le_add (hC n) (hC' n)
    _ ≤ |C| * (1 + ‖n‖) ^ (k + k') + |C'| * (1 + ‖n‖) ^ (k + k') :=
        add_le_add (mul_le_mul (le_abs_self C) hk (by positivity) (abs_nonneg C))
          (mul_le_mul (le_abs_self C') hk' (by positivity) (abs_nonneg C'))
    _ = (|C| + |C'|) * (1 + ‖n‖) ^ (k + k') := by ring

theorem IsPolyBounded.mul {m m' : (ι → ℤ) → ℂ} (hm : IsPolyBounded m) (hm' : IsPolyBounded m') :
    IsPolyBounded fun n => m n * m' n := by
  obtain ⟨C, k, hC⟩ := hm
  obtain ⟨C', k', hC'⟩ := hm'
  refine ⟨C * C', k + k', fun n => ?_⟩
  rw [norm_mul]
  calc ‖m n‖ * ‖m' n‖ ≤ (C * (1 + ‖n‖) ^ k) * (C' * (1 + ‖n‖) ^ k') :=
        mul_le_mul (hC n) (hC' n) (norm_nonneg _) ((norm_nonneg _).trans (hC n))
    _ = C * C' * (1 + ‖n‖) ^ (k + k') := by ring

theorem IsPolyBounded.pow {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m) (k : ℕ) :
    IsPolyBounded fun n => m n ^ k := by
  induction k with
  | zero => simpa using isPolyBounded_const (ι := ι) 1
  | succ k ih => simpa only [pow_succ] using ih.mul hm

/-- The symbol `n ↦ 2πi ⟨n, v⟩` of the directional derivative `∂_v` is polynomially bounded. -/
theorem isPolyBounded_derivSymbol (v : ι → ℝ) :
    IsPolyBounded fun n : ι → ℤ => 2 * π * I * ∑ i, (n i : ℂ) * (v i : ℂ) := by
  refine ⟨2 * π * ∑ i, ‖v i‖, 1, fun n => ?_⟩
  have h1 : ‖∑ i, (n i : ℂ) * (v i : ℂ)‖ ≤ (1 + ‖n‖) * ∑ i, ‖v i‖ := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_intCast, ← Int.norm_eq_abs, Complex.norm_real]
    gcongr
    linarith [norm_le_pi_norm n i]
  have h2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [norm_mul, h2, pow_one]
  calc 2 * π * ‖∑ i, (n i : ℂ) * (v i : ℂ)‖ ≤ 2 * π * ((1 + ‖n‖) * ∑ i, ‖v i‖) := by
        gcongr
    _ = 2 * π * (∑ i, ‖v i‖) * (1 + ‖n‖) := by ring

/-! ### Fourier multipliers on smooth periodic functions -/

/-- The Fourier multiplier with symbol `m : ℤ^ι → ℂ` on periodic functions:
`T_m g (x) = Σ_n m (n) ĝ (n) e^{2πi ⟨n, x⟩}` (`0` where the series does not converge; it
converges absolutely for smooth periodic `g` and polynomially bounded `m`). -/
def periodicMultiplier (m : (ι → ℤ) → ℂ) (g : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℂ :=
  ∑' n, m n * cubeFourierCoeff g n * mFourier n (ofPi x)

theorem isPeriodic_periodicMultiplier (m : (ι → ℤ) → ℂ) (g : (ι → ℝ) → ℂ) :
    IsPeriodic (periodicMultiplier m g) :=
  fun x k => by simp only [periodicMultiplier, ofPi_add_int]

/-- The weighted coefficients `(1 + ‖n‖)^j |m (n) ĝ (n)|` are summable. -/
private lemma summable_symbol_mul_cubeFourierCoeff {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) (j : ℕ) :
    Summable fun n => (1 + ‖n‖) ^ j * ‖m n * cubeFourierCoeff g n‖ := by
  obtain ⟨C, k, hC⟩ := hm
  refine ((summable_cubeFourierCoeff hg hper (j + k)).mul_left |C|).of_nonneg_of_le
    (fun n => by positivity) fun n => ?_
  rw [norm_mul]
  calc (1 + ‖n‖) ^ j * (‖m n‖ * ‖cubeFourierCoeff g n‖)
      ≤ (1 + ‖n‖) ^ j * ((|C| * (1 + ‖n‖) ^ k) * ‖cubeFourierCoeff g n‖) := by
        gcongr
        exact (hC n).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    _ = |C| * ((1 + ‖n‖) ^ (j + k) * ‖cubeFourierCoeff g n‖) := by ring

private lemma summable_symbol_mul {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) :
    Summable fun n => m n * cubeFourierCoeff g n :=
  Summable.of_norm (by simpa using summable_symbol_mul_cubeFourierCoeff hm hg hper 0)

/-- The terms of the series of `T_m g (x)` are summable. -/
private lemma summable_periodicMultiplier_terms {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) (x : ι → ℝ) :
    Summable fun n => m n * cubeFourierCoeff g n * mFourier n (ofPi x) :=
  Summable.of_norm (by
    simpa [norm_mFourier_ofPi] using (summable_symbol_mul hm hg hper).norm)

/-- The linear functional `ℓ_n x = 2πi ⟨n, x⟩`, with `e_n (x) = exp (ℓ_n x)`. -/
private def freqCLM (n : ι → ℤ) : (ι → ℝ) →L[ℝ] ℂ :=
  ∑ i, (2 * π * I * (n i : ℂ)) • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

private lemma freqCLM_apply (n : ι → ℤ) (x : ι → ℝ) :
    freqCLM n x = 2 * π * I * ∑ i, (n i : ℂ) * (x i : ℂ) := by
  simp [freqCLM, Finset.mul_sum, mul_assoc]

private lemma mFourier_ofPi_eq_exp (n : ι → ℤ) (x : ι → ℝ) :
    mFourier n (ofPi x) = cexp (freqCLM n x) := by
  rw [mFourier_ofPi, freqCLM_apply]

private lemma norm_freqCLM_le (n : ι → ℤ) :
    ‖freqCLM n‖ ≤ 2 * π * Fintype.card ι * (1 + ‖n‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [freqCLM_apply]
  have h2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [norm_mul, h2]
  have h1 : ‖∑ i, (n i : ℂ) * (x i : ℂ)‖ ≤ Fintype.card ι * ((1 + ‖n‖) * ‖x‖) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖(n i : ℂ) * (x i : ℂ)‖ ≤ ∑ _i : ι, (1 + ‖n‖) * ‖x‖ :=
          Finset.sum_le_sum fun i _ => by
            rw [norm_mul, Complex.norm_intCast, ← Int.norm_eq_abs, Complex.norm_real]
            exact mul_le_mul (by linarith [norm_le_pi_norm n i]) (norm_le_pi_norm x i)
              (norm_nonneg _) (by positivity)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc 2 * π * ‖∑ i, (n i : ℂ) * (x i : ℂ)‖
      ≤ 2 * π * (Fintype.card ι * ((1 + ‖n‖) * ‖x‖)) := by gcongr
    _ = 2 * π * Fintype.card ι * (1 + ‖n‖) * ‖x‖ := by ring

/-- `‖D^k (exp ∘ ℓ)‖ ≤ ‖ℓ‖^k |exp ∘ ℓ|` for a continuous linear functional `ℓ`. -/
private lemma norm_iteratedFDeriv_cexp_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℂ) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => cexp (ℓ y)) x‖ ≤ ‖ℓ‖ ^ k * ‖cexp (ℓ x)‖ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    let Φ : ℂ →L[ℝ] (E →L[ℝ] ℂ) := (ContinuousLinearMap.lsmul ℝ ℂ).flip ℓ
    have hF : fderiv ℝ (fun y => cexp (ℓ y)) = fun y => Φ (cexp (ℓ y)) := by
      funext y
      rw [(ℓ.hasFDerivAt.cexp).fderiv]
      rfl
    have hΦ : ‖Φ‖ ≤ ‖ℓ‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => by
      simp [Φ, norm_smul, mul_comm]
    rw [← norm_iteratedFDeriv_fderiv, hF]
    calc ‖iteratedFDeriv ℝ k (fun y => Φ (cexp (ℓ y))) x‖
        ≤ ‖Φ‖ * ‖iteratedFDeriv ℝ k (fun y => cexp (ℓ y)) x‖ :=
          Φ.norm_iteratedFDeriv_comp_left (f := fun y => cexp (ℓ y))
            (ℓ.contDiff.cexp.contDiffAt (n := ⊤)) le_top
      _ ≤ ‖ℓ‖ * (‖ℓ‖ ^ k * ‖cexp (ℓ x)‖) := by gcongr; exact ih x
      _ = ‖ℓ‖ ^ (k + 1) * ‖cexp (ℓ x)‖ := by ring

/-- `T_m g` is smooth, by the Weierstrass M-test for the series of the derivatives of every order
(`contDiff_tsum`), whose terms are `O ((1 + ‖n‖)^{k + j} |ĝ (n)|)`. -/
theorem contDiff_periodicMultiplier {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) :
    ContDiff ℝ ∞ (periodicMultiplier m g) := by
  set c : (ι → ℤ) → ℂ := fun n => m n * cubeFourierCoeff g n with hc
  have hfun : periodicMultiplier m g = fun x => ∑' n, c n * cexp (freqCLM n x) := by
    funext x
    simp only [periodicMultiplier, hc, mFourier_ofPi_eq_exp]
  rw [hfun]
  refine contDiff_tsum (v := fun j n => ‖c n‖ * (2 * π * Fintype.card ι * (1 + ‖n‖)) ^ j)
    (fun n => contDiff_const.mul (freqCLM n).contDiff.cexp) (fun j _ => ?_)
    (fun j n x _ => ?_)
  · refine ((summable_symbol_mul_cubeFourierCoeff hm hg hper j).mul_left
      ((2 * π * Fintype.card ι) ^ j)).congr fun n => ?_
    simp only [hc, mul_pow]
    ring
  · have hsmul : (fun x => c n * cexp (freqCLM n x)) = fun x => c n • cexp (freqCLM n x) := rfl
    rw [hsmul, iteratedFDeriv_const_smul_apply' (freqCLM n).contDiff.cexp.contDiffAt, norm_smul]
    have h1 := norm_iteratedFDeriv_cexp_clm (freqCLM n) j x
    rw [← mFourier_ofPi_eq_exp, norm_mFourier_ofPi, mul_one] at h1
    gcongr
    exact h1.trans (pow_le_pow_left₀ (norm_nonneg _) (norm_freqCLM_le n) j)

/-- The coefficients of `T_m g` are `m ĝ`, by termwise integration. -/
theorem cubeFourierCoeff_periodicMultiplier {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) (n : ι → ℤ) :
    cubeFourierCoeff (periodicMultiplier m g) n = m n * cubeFourierCoeff g n :=
  cubeFourierCoeff_tsum_mFourier (c := fun n => m n * cubeFourierCoeff g n)
    (summable_symbol_mul hm hg hper) n

/-- `T_m T_{m'} = T_{m m'}` on smooth periodic functions. -/
theorem periodicMultiplier_periodicMultiplier {m m' : (ι → ℤ) → ℂ} (hm : IsPolyBounded m)
    (hm' : IsPolyBounded m') {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) :
    periodicMultiplier m (periodicMultiplier m' g) =
      periodicMultiplier (fun n => m n * m' n) g := by
  have h1 := contDiff_periodicMultiplier hm' hg hper
  have h2 := isPeriodic_periodicMultiplier m' g
  refine eq_of_cubeFourierCoeff_eq (contDiff_periodicMultiplier hm h1 h2)
    (isPeriodic_periodicMultiplier _ _) (contDiff_periodicMultiplier (hm.mul hm') hg hper)
    (isPeriodic_periodicMultiplier _ _) fun n => ?_
  rw [cubeFourierCoeff_periodicMultiplier hm h1 h2, cubeFourierCoeff_periodicMultiplier hm' hg hper,
    cubeFourierCoeff_periodicMultiplier (hm.mul hm') hg hper, mul_assoc]

/-- `T_1 = id` on smooth periodic functions: the Fourier series converges to the function. -/
theorem periodicMultiplier_one {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) :
    periodicMultiplier (fun _ => 1) g = g := by
  funext x
  simpa [periodicMultiplier] using (hasSum_cubeFourierCoeff_mul_mFourier hg hper x).tsum_eq

/-- `T_m ∂_v = T_{2πi ⟨·, v⟩ m}` on smooth periodic functions. -/
theorem periodicMultiplier_fderiv {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) (v : ι → ℝ) :
    periodicMultiplier m (fun x => fderiv ℝ g x v) =
      periodicMultiplier (fun n => 2 * π * I * (∑ i, (n i : ℂ) * (v i : ℂ)) * m n) g := by
  have h1 := contDiff_fderiv_apply hg v
  have h2 := hper.fderiv_apply v
  have hm' := (isPolyBounded_derivSymbol v).mul hm
  refine eq_of_cubeFourierCoeff_eq (contDiff_periodicMultiplier hm h1 h2)
    (isPeriodic_periodicMultiplier _ _) (contDiff_periodicMultiplier hm' hg hper)
    (isPeriodic_periodicMultiplier _ _) fun n => ?_
  rw [cubeFourierCoeff_periodicMultiplier hm h1 h2, cubeFourierCoeff_periodicMultiplier hm' hg hper,
    cubeFourierCoeff_fderiv_of_contDiff (contDiff_one_of_infty hg) hper]
  ring

/-- Coefficients of the sum of two smooth periodic functions. -/
private lemma cubeFourierCoeff_add_of_contDiff {g h : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgp : IsPeriodic g) (hh : ContDiff ℝ ∞ h) (hhp : IsPeriodic h) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => g x + h x) n = cubeFourierCoeff g n + cubeFourierCoeff h n := by
  obtain ⟨C, hC⟩ := hgp.exists_bound hg.continuous
  obtain ⟨D, hD⟩ := hhp.exists_bound hh.continuous
  exact cubeFourierCoeff_add hg.continuous.aestronglyMeasurable hC
    hh.continuous.aestronglyMeasurable hD n

private lemma cubeFourierCoeff_sub_of_contDiff {g h : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgp : IsPeriodic g) (hh : ContDiff ℝ ∞ h) (hhp : IsPeriodic h) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => g x - h x) n = cubeFourierCoeff g n - cubeFourierCoeff h n := by
  obtain ⟨C, hC⟩ := hgp.exists_bound hg.continuous
  obtain ⟨D, hD⟩ := hhp.exists_bound hh.continuous
  exact cubeFourierCoeff_sub hg.continuous.aestronglyMeasurable hC
    hh.continuous.aestronglyMeasurable hD n

theorem periodicMultiplier_add {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m) {g h : (ι → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodic g) (hh : ContDiff ℝ ∞ h) (hhp : IsPeriodic h) :
    periodicMultiplier m (fun x => g x + h x) =
      fun x => periodicMultiplier m g x + periodicMultiplier m h x := by
  funext x
  simp only [periodicMultiplier]
  rw [← (summable_periodicMultiplier_terms hm hg hgp x).tsum_add
    (summable_periodicMultiplier_terms hm hh hhp x)]
  congr 1
  funext n
  rw [cubeFourierCoeff_add_of_contDiff hg hgp hh hhp]
  ring

theorem periodicMultiplier_sub {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m) {g h : (ι → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodic g) (hh : ContDiff ℝ ∞ h) (hhp : IsPeriodic h) :
    periodicMultiplier m (fun x => g x - h x) =
      fun x => periodicMultiplier m g x - periodicMultiplier m h x := by
  funext x
  simp only [periodicMultiplier]
  rw [← (summable_periodicMultiplier_terms hm hg hgp x).tsum_sub
    (summable_periodicMultiplier_terms hm hh hhp x)]
  congr 1
  funext n
  rw [cubeFourierCoeff_sub_of_contDiff hg hgp hh hhp]
  ring

theorem periodicMultiplier_const_mul (m : (ι → ℤ) → ℂ) (c : ℂ) (g : (ι → ℝ) → ℂ) :
    periodicMultiplier m (fun x => c * g x) = fun x => c * periodicMultiplier m g x := by
  funext x
  simp only [periodicMultiplier, cubeFourierCoeff_const_mul]
  rw [← tsum_mul_left]
  congr 1
  funext n
  ring

/-- `T_m` on trigonometric polynomials. -/
theorem periodicMultiplier_sum_mFourier (m : (ι → ℤ) → ℂ) (S : Finset (ι → ℤ))
    (c : (ι → ℤ) → ℂ) :
    periodicMultiplier m (fun x => ∑ n ∈ S, c n * mFourier n (ofPi x)) =
      fun x => ∑ n ∈ S, m n * c n * mFourier n (ofPi x) := by
  funext x
  simp only [periodicMultiplier, cubeFourierCoeff_trig]
  rw [tsum_eq_sum (s := S) fun n hn => by simp [hn]]
  exact Finset.sum_congr rfl fun n hn => by simp [hn]

/-! ### The Wirtinger derivatives on `ℝ² ≅ ℂ` and the inverse of `∂_zbar`

With `ℝ² ≅ ℂ` by `(x, y) ↦ x + iy`, and the lattice point `ν = n₀ + i n₁` of `n ∈ ℤ²`
(`HarmonicAnalysis.latticePoint`). -/

section Two

/-- The Wirtinger derivative `∂g = ½ (∂_x g − i ∂_y g)` of `g : ℝ² → ℂ`. -/
def dzPi (g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  2⁻¹ * (fderiv ℝ g x (Pi.single 0 1) - I * fderiv ℝ g x (Pi.single 1 1))

/-- The Wirtinger derivative `∂_zbar g = ½ (∂_x g + i ∂_y g)` of `g : ℝ² → ℂ`. -/
def dzbarPi (g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  2⁻¹ * (fderiv ℝ g x (Pi.single 0 1) + I * fderiv ℝ g x (Pi.single 1 1))

theorem contDiff_dzPi {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (dzPi g) :=
  contDiff_const.mul ((contDiff_fderiv_apply hg _).sub
    (contDiff_const.mul (contDiff_fderiv_apply hg _)))

theorem contDiff_dzbarPi {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (dzbarPi g) :=
  contDiff_const.mul ((contDiff_fderiv_apply hg _).add
    (contDiff_const.mul (contDiff_fderiv_apply hg _)))

theorem isPeriodic_dzPi {g : (Fin 2 → ℝ) → ℂ} (hper : IsPeriodic g) : IsPeriodic (dzPi g) := by
  intro x k
  have h0 := hper.fderiv_apply (Pi.single 0 1) x k
  have h1 := hper.fderiv_apply (Pi.single 1 1) x k
  simp only at h0 h1
  simp only [dzPi, h0, h1]

theorem isPeriodic_dzbarPi {g : (Fin 2 → ℝ) → ℂ} (hper : IsPeriodic g) :
    IsPeriodic (dzbarPi g) := by
  intro x k
  have h0 := hper.fderiv_apply (Pi.single 0 1) x k
  have h1 := hper.fderiv_apply (Pi.single 1 1) x k
  simp only at h0 h1
  simp only [dzbarPi, h0, h1]

/-- The coefficients of `∂_x g` and `∂_y g` for `C¹` periodic `g` on `ℝ²`. -/
private lemma cubeFourierCoeff_partial {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) (n : Fin 2 → ℤ) :
    cubeFourierCoeff (fun x => fderiv ℝ g x (Pi.single 0 1)) n =
        2 * π * I * (n 0 : ℂ) * cubeFourierCoeff g n ∧
      cubeFourierCoeff (fun x => fderiv ℝ g x (Pi.single 1 1)) n =
        2 * π * I * (n 1 : ℂ) * cubeFourierCoeff g n := by
  rw [cubeFourierCoeff_fderiv_of_contDiff hg hper, cubeFourierCoeff_fderiv_of_contDiff hg hper]
  simp [Fin.sum_univ_two]

/-- The bounds that the linearity of the coefficients needs, for `∂_x g` and `I ∂_y g`. -/
private lemma exists_bound_partial {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) (v : Fin 2 → ℝ) (c : ℂ) :
    Continuous (fun x => c * fderiv ℝ g x v) ∧ ∃ C, ∀ x, ‖c * fderiv ℝ g x v‖ ≤ C := by
  have hc : Continuous fun x => c * fderiv ℝ g x v :=
    continuous_const.mul ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  refine ⟨hc, ?_⟩
  have hp : IsPeriodic fun x => c * fderiv ℝ g x v := by
    intro x k
    have := hper.fderiv_apply v x k
    simp only at this
    simp only [this]
  exact hp.exists_bound hc

/-- The symbol of `∂_zbar`: `(∂_zbar g)^ (n) = πi (n₀ + i n₁) ĝ (n)`. -/
theorem cubeFourierCoeff_dzbarPi {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) (n : Fin 2 → ℤ) :
    cubeFourierCoeff (dzbarPi g) n =
      π * I * HarmonicAnalysis.latticePoint n * cubeFourierCoeff g n := by
  obtain ⟨h0c, C0, hC0⟩ := exists_bound_partial hg hper (Pi.single 0 1) 1
  obtain ⟨h1c, C1, hC1⟩ := exists_bound_partial hg hper (Pi.single 1 1) I
  simp only [one_mul] at h0c hC0
  obtain ⟨e0, e1⟩ := cubeFourierCoeff_partial hg hper n
  have e : dzbarPi g =
      fun x => 2⁻¹ * (fderiv ℝ g x (Pi.single 0 1) + I * fderiv ℝ g x (Pi.single 1 1)) := rfl
  rw [e, cubeFourierCoeff_const_mul, cubeFourierCoeff_add h0c.aestronglyMeasurable hC0
    h1c.aestronglyMeasurable hC1, cubeFourierCoeff_const_mul, e0, e1]
  simp only [HarmonicAnalysis.latticePoint]
  ring

/-- The symbol of `∂`: `(∂g)^ (n) = πi (n₀ − i n₁) ĝ (n)`. -/
theorem cubeFourierCoeff_dzPi {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) (n : Fin 2 → ℤ) :
    cubeFourierCoeff (dzPi g) n =
      π * I * conj (HarmonicAnalysis.latticePoint n) * cubeFourierCoeff g n := by
  obtain ⟨h0c, C0, hC0⟩ := exists_bound_partial hg hper (Pi.single 0 1) 1
  obtain ⟨h1c, C1, hC1⟩ := exists_bound_partial hg hper (Pi.single 1 1) I
  simp only [one_mul] at h0c hC0
  obtain ⟨e0, e1⟩ := cubeFourierCoeff_partial hg hper n
  have e : dzPi g =
      fun x => 2⁻¹ * (fderiv ℝ g x (Pi.single 0 1) - I * fderiv ℝ g x (Pi.single 1 1)) := rfl
  rw [e, cubeFourierCoeff_const_mul, cubeFourierCoeff_sub h0c.aestronglyMeasurable hC0
    h1c.aestronglyMeasurable hC1, cubeFourierCoeff_const_mul, e0, e1]
  simp only [HarmonicAnalysis.latticePoint, map_add, map_mul, map_intCast, conj_I]
  ring

/-- `∂_zbar g` has mean zero. -/
theorem cubeFourierCoeff_dzbarPi_zero {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) : cubeFourierCoeff (dzbarPi g) 0 = 0 := by
  rw [cubeFourierCoeff_dzbarPi hg hper]
  simp [HarmonicAnalysis.latticePoint]

/-- `∂g` has mean zero. -/
theorem cubeFourierCoeff_dzPi_zero {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) : cubeFourierCoeff (dzPi g) 0 = 0 := by
  rw [cubeFourierCoeff_dzPi hg hper]
  simp [HarmonicAnalysis.latticePoint]

/-- The symbol of `∂_zbar⁻¹` on mean-zero functions: `(πi (n₀ + i n₁))⁻¹` for `n ≠ 0`, and `0` at
`n = 0`. -/
def dzbarInvSymbol (n : Fin 2 → ℤ) : ℂ :=
  if n = 0 then 0 else (π * I * HarmonicAnalysis.latticePoint n)⁻¹

/-- A nonzero `n ∈ ℤ^ι` has sup norm at least `1`. -/
private lemma one_le_norm_of_ne_zero {n : ι → ℤ} (hn : n ≠ 0) : 1 ≤ ‖n‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  refine le_trans ?_ (norm_le_pi_norm n i)
  rw [Int.norm_eq_abs, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hi

private lemma latticePoint_ne_zero {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    HarmonicAnalysis.latticePoint n ≠ 0 := by
  have h1 := one_le_norm_of_ne_zero hn
  have h2 := HarmonicAnalysis.norm_le_norm_latticePoint n
  intro h
  rw [h, norm_zero] at h2
  linarith

theorem isPolyBounded_dzbarInvSymbol : IsPolyBounded dzbarInvSymbol := by
  refine isPolyBounded_of_norm_le (C := 1) fun n => ?_
  unfold dzbarInvSymbol
  split_ifs with hn
  · simp
  · have h1 := one_le_norm_of_ne_zero hn
    have h2 := HarmonicAnalysis.norm_le_norm_latticePoint n
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    apply inv_le_one_of_one_le₀
    nlinarith [Real.two_le_pi]

/-- `∂_zbar (T h) = h` for the multiplier `T` with symbol `dzbarInvSymbol` and every smooth periodic
`h` of mean zero, by comparing coefficients. -/
theorem dzbarPi_periodicMultiplier_dzbarInvSymbol {h : (Fin 2 → ℝ) → ℂ} (hh : ContDiff ℝ ∞ h)
    (hper : IsPeriodic h) (h0 : cubeFourierCoeff h 0 = 0) :
    dzbarPi (periodicMultiplier dzbarInvSymbol h) = h := by
  have hu := contDiff_periodicMultiplier isPolyBounded_dzbarInvSymbol hh hper
  have hup := isPeriodic_periodicMultiplier dzbarInvSymbol h
  refine eq_of_cubeFourierCoeff_eq (contDiff_dzbarPi hu) (isPeriodic_dzbarPi hup) hh hper
    fun n => ?_
  rw [cubeFourierCoeff_dzbarPi (contDiff_one_of_infty hu) hup,
    cubeFourierCoeff_periodicMultiplier isPolyBounded_dzbarInvSymbol hh hper]
  unfold dzbarInvSymbol
  split_ifs with hn
  · subst hn; simp [h0]
  · have hne : (π : ℂ) * I * HarmonicAnalysis.latticePoint n ≠ 0 :=
      mul_ne_zero (mul_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero) I_ne_zero)
        (latticePoint_ne_zero hn)
    exact mul_inv_cancel_left₀ hne _

/-- Every smooth periodic `h` of mean zero is `∂_zbar u` for a smooth periodic `u` of mean zero. -/
theorem exists_dzbarPi_eq {h : (Fin 2 → ℝ) → ℂ} (hh : ContDiff ℝ ∞ h) (hper : IsPeriodic h)
    (h0 : cubeFourierCoeff h 0 = 0) :
    ∃ u, ContDiff ℝ ∞ u ∧ IsPeriodic u ∧ cubeFourierCoeff u 0 = 0 ∧ dzbarPi u = h := by
  refine ⟨periodicMultiplier dzbarInvSymbol h,
    contDiff_periodicMultiplier isPolyBounded_dzbarInvSymbol hh hper,
    isPeriodic_periodicMultiplier _ _, ?_, dzbarPi_periodicMultiplier_dzbarInvSymbol hh hper h0⟩
  rw [cubeFourierCoeff_periodicMultiplier isPolyBounded_dzbarInvSymbol hh hper]
  simp [dzbarInvSymbol]

end Two

end UnitAddTorus

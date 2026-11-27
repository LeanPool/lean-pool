/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.Cube
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Fourier coefficients over the unit cube, and derivatives of Lipschitz periodic functions

For a function `g : ℝ^ι → ℂ`, its Fourier coefficients over the open unit cube `(0, 1)^ι`
(`UnitAddTorus.cubeFourierCoeff`) are `ĝ (n) = ∫_{(0,1)^ι} e^{−2πi ⟨n, x⟩} g (x) dx`, `n ∈ ℤ^ι`;
for a `ℤ^ι`-periodic `g` they are the Fourier coefficients on the torus `𝕋^ι` of the function that
`g` induces there (Grafakos, *Classical Fourier Analysis*, Chapter 3).

* Linearity (`UnitAddTorus.cubeFourierCoeff_add`, `UnitAddTorus.cubeFourierCoeff_sub`,
  `UnitAddTorus.cubeFourierCoeff_const_mul`), for bounded measurable functions, and the
  coefficients of a trigonometric polynomial (`UnitAddTorus.cubeFourierCoeff_trig`,
  `UnitAddTorus.cubeFourierCoeff_one`), by the orthogonality of the monomials `e_n`.
* Parseval's identity `Σ_n |ĝ (n)|² = ∫_{(0,1)^ι} |g|²` for bounded measurable periodic `g`
  (`UnitAddTorus.hasSum_sq_cubeFourierCoeff`), from Mathlib's Parseval identity on the torus.
* The coefficients of a derivative: for a Lipschitz `ℤ^ι`-periodic `f : ℝ^ι → ℝ`,
  `(∂_v f)^ (n) = 2πi ⟨n, v⟩ f̂ (n)`, with `∂_v f (x) = fderiv ℝ f x v`, which is the derivative of
  `f` almost everywhere by Rademacher's theorem (`UnitAddTorus.cubeFourierCoeff_fderiv`). The
  proof integrates the difference quotients against `e_{−n}`, moves the translation onto `e_{−n}`
  and passes to the limit by dominated convergence.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Complex
open scoped ComplexConjugate Real Finset

/-! As in `Mathlib.Analysis.Fourier.AddCircleMulti` (whose local instances these are), the measure
on `ℝ / ℤ` is the Haar measure of total mass one. -/
attribute [local instance] instMeasureSpaceUnitAddCircle instIsAddHaarMeasureUnitAddCircleVolume
  instIsProbabilityMeasureUnitAddCircleVolume

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-! ### Fourier coefficients over the cube -/

/-- The `n`-th Fourier coefficient of a function on `ℝ^ι`, over the cube:
`ĝ (n) = ∫_{(0,1)^ι} e^{−2πi ⟨n, x⟩} g (x) dx`. -/
def cubeFourierCoeff (g : (ι → ℝ) → ℂ) (n : ι → ℤ) : ℂ :=
  ∫ x in cube ι, mFourier (-n) (ofPi x) * g x

theorem integrableOn_cube_of_bound {E : Type*} [NormedAddCommGroup E] {g : (ι → ℝ) → E}
    (hg : AEStronglyMeasurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) : IntegrableOn g (cube ι) :=
  Measure.integrableOn_of_bounded (by rw [volume_cube]; exact ENNReal.one_ne_top) hg
    (ae_of_all _ hC)

theorem integrableOn_cube_mFourier_mul {g : (ι → ℝ) → ℂ} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) (n : ι → ℤ) :
    IntegrableOn (fun x => mFourier n (ofPi x) * g x) (cube ι) :=
  integrableOn_cube_of_bound ((continuous_mFourier_ofPi n).aestronglyMeasurable.mul hg)
    (C := C) fun x => by rw [norm_mul, norm_mFourier_ofPi, one_mul]; exact hC x

theorem cubeFourierCoeff_add {g h : (ι → ℝ) → ℂ} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (hh : AEStronglyMeasurable h) {D : ℝ} (hhD : ∀ x, ‖h x‖ ≤ D)
    (n : ι → ℤ) :
    cubeFourierCoeff (fun x => g x + h x) n = cubeFourierCoeff g n + cubeFourierCoeff h n := by
  simp only [cubeFourierCoeff, mul_add]
  exact integral_add (integrableOn_cube_mFourier_mul hg hgC _)
    (integrableOn_cube_mFourier_mul hh hhD _)

theorem cubeFourierCoeff_sub {g h : (ι → ℝ) → ℂ} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (hh : AEStronglyMeasurable h) {D : ℝ} (hhD : ∀ x, ‖h x‖ ≤ D)
    (n : ι → ℤ) :
    cubeFourierCoeff (fun x => g x - h x) n = cubeFourierCoeff g n - cubeFourierCoeff h n := by
  simp only [cubeFourierCoeff, mul_sub]
  exact integral_sub (integrableOn_cube_mFourier_mul hg hgC _)
    (integrableOn_cube_mFourier_mul hh hhD _)

theorem cubeFourierCoeff_const_mul (c : ℂ) (g : (ι → ℝ) → ℂ) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => c * g x) n = c * cubeFourierCoeff g n := by
  simp only [cubeFourierCoeff, mul_left_comm _ c]
  exact integral_const_mul c _

/-- The coefficients of a trigonometric polynomial. -/
theorem cubeFourierCoeff_trig (S : Finset (ι → ℤ)) (c : (ι → ℤ) → ℂ) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => ∑ m ∈ S, c m * mFourier m (ofPi x)) n =
      if n ∈ S then c n else 0 := by
  simp only [cubeFourierCoeff, Finset.mul_sum]
  rw [integral_finsetSum]
  · have : ∀ m ∈ S, ∫ x in cube ι, mFourier (-n) (ofPi x) * (c m * mFourier m (ofPi x)) =
        if n = m then c m else 0 := by
      intro m _
      have e : ∀ x, mFourier (-n) (ofPi x) * (c m * mFourier m (ofPi x)) =
          c m * mFourier (-n + m) (ofPi x) := fun x => by
        rw [mFourier_ofPi_add_index]; ring
      simp_rw [e]
      rw [integral_const_mul, integral_cube_mFourier]
      by_cases h : n = m
      · simp [h]
      · have h' : -n + m ≠ 0 := fun h0 => h (neg_add_eq_zero.mp h0)
        simp [h, h']
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  · intro m _
    exact integrableOn_cube_of_bound ((continuous_mFourier_ofPi _).mul
      (continuous_const.mul (continuous_mFourier_ofPi _))).aestronglyMeasurable (C := ‖c m‖)
      fun x => by rw [norm_mul, norm_mul, norm_mFourier_ofPi, norm_mFourier_ofPi]; simp

/-- The coefficients of the constant `1`. -/
theorem cubeFourierCoeff_one (n : ι → ℤ) :
    cubeFourierCoeff (fun _ => (1 : ℂ)) n = if n = 0 then 1 else 0 := by
  rw [cubeFourierCoeff]
  simp only [mul_one]
  rw [integral_cube_mFourier]
  simp only [neg_eq_zero]

/-- **Parseval's identity** on the cube, for a bounded measurable `ℤ^ι`-periodic `g`:
`Σ_n |ĝ (n)|² = ∫_{(0,1)^ι} |g|²`. -/
theorem hasSum_sq_cubeFourierCoeff {g : (ι → ℝ) → ℂ} (hgm : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (hg : IsPeriodic g) :
    HasSum (fun n => ‖cubeFourierCoeff g n‖ ^ 2) (∫ x in cube ι, ‖g x‖ ^ 2) := by
  set G : UnitAddTorus ι → ℂ := g ∘ toPi with hG
  have hGm : Measurable G := hgm.comp measurable_toPi
  have hmem : MemLp G 2 volume := MemLp.of_bound hGm.aestronglyMeasurable C
    (ae_of_all _ fun z => hgC _)
  have key := hasSum_sq_mFourierCoeff (hmem.toLp G)
  have hc : ∀ n, mFourierCoeff (hmem.toLp G) n = cubeFourierCoeff g n := by
    intro n
    have e1 : mFourierCoeff (hmem.toLp G) n = mFourierCoeff G n := by
      refine integral_congr_ae ?_
      filter_upwards [hmem.coeFn_toLp] with z hz
      rw [hz]
    rw [e1, mFourierCoeff, cubeFourierCoeff, ← integral_cube_ofPi]
    refine setIntegral_congr_fun measurableSet_cube fun x _ => ?_
    simp only [hG, Function.comp_apply, hg.comp_toPi_ofPi, smul_eq_mul]
  have hn : ∫ t, ‖(hmem.toLp G) t‖ ^ 2 = ∫ x in cube ι, ‖g x‖ ^ 2 := by
    have e1 : ∫ t, ‖(hmem.toLp G) t‖ ^ 2 = ∫ t, ‖G t‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hmem.coeFn_toLp] with z hz
      rw [hz]
    rw [e1, ← integral_cube_ofPi]
    refine setIntegral_congr_fun measurableSet_cube fun x _ => ?_
    simp only [hG, Function.comp_apply, hg.comp_toPi_ofPi]
  simp only [hc, hn] at key
  exact key

theorem integrableOn_cube_of_continuous {E : Type*} [NormedAddCommGroup E] {g : (ι → ℝ) → E}
    (hg : Continuous g) : IntegrableOn g (cube ι) :=
  (hg.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc
    (a := (0 : ℝ)) (b := 1))).mono_set (pi_mono fun _ _ => Ioo_subset_Icc_self)

/-! ### The derivative of a Lipschitz periodic function -/

/-- The slope `t⁻¹ (e^{2πi t ⟨n, v⟩} − 1)` tends to `2πi ⟨n, v⟩`. -/
theorem tendsto_slope_mFourier_ofPi_smul (n : ι → ℤ) (v : ι → ℝ) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℂ) * (mFourier n (ofPi (t • v)) - 1)) (𝓝[≠] 0)
      (𝓝 (2 * π * I * ∑ i, (n i : ℂ) * (v i : ℂ))) := by
  set c : ℂ := 2 * π * I * ∑ i, (n i : ℂ) * (v i : ℂ) with hc
  have hE : ∀ t : ℝ, mFourier n (ofPi (t • v)) = Complex.exp ((t : ℂ) * c) := fun t => by
    rw [mFourier_ofPi, hc]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c)) c 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * c) c 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const c
    simpa using h1.cexp
  have := hasDerivAt_iff_tendsto_slope_zero.mp hd
  simp only [zero_add, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at this
  refine this.congr fun t => ?_
  rw [hE, Complex.real_smul, Complex.ofReal_inv]

/-- The Fourier coefficients of the derivative of a Lipschitz `ℤ^ι`-periodic `f : ℝ^ι → ℝ` in the
direction `v`: `(∂_v f)^ (n) = 2πi ⟨n, v⟩ f̂ (n)`, with `∂_v f (x) = fderiv ℝ f x v` (the derivative
almost everywhere, by Rademacher's theorem). The proof integrates the difference quotients
`t⁻¹ (f (x + t v) − f (x))` against `e_{−n}`, moves the translation onto `e_{−n}` by the
translation invariance of the integral of a periodic function, and lets `t → 0` (dominated
convergence on one side, the derivative of `t ↦ e^{2πi t ⟨n, v⟩}` on the other). -/
theorem cubeFourierCoeff_fderiv {f : (ι → ℝ) → ℝ} {C : NNReal} (hf : LipschitzWith C f)
    (hper : IsPeriodic f) (v : ι → ℝ) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => (fderiv ℝ f x v : ℂ)) n =
      2 * π * I * (∑ i, (n i : ℂ) * (v i : ℂ)) * cubeFourierCoeff (fun x => (f x : ℂ)) n := by
  set A : ℝ → ℂ := fun t => ∫ x in cube ι,
    mFourier (-n) (ofPi x) * ((t⁻¹ * (f (x + t • v) - f x) : ℝ) : ℂ) with hA
  -- the difference quotients converge to the derivative
  have h1 : Tendsto A (𝓝[≠] 0) (𝓝 (cubeFourierCoeff (fun x => (fderiv ℝ f x v : ℂ)) n)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (C : ℝ) * ‖v‖) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t => ((continuous_mFourier_ofPi _).mul
        (Complex.continuous_ofReal.comp (continuous_const.mul
          ((hf.continuous.comp (continuous_id.add continuous_const)).sub
            hf.continuous)))).aestronglyMeasurable
    · refine Eventually.of_forall fun t => ae_of_all _ fun x => ?_
      rw [norm_mul, norm_mFourier_ofPi, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_inv]
      have h := hf.dist_le_mul (x + t • v) x
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
      by_cases ht : t = 0
      · simp only [ht, abs_zero, inv_zero, zero_mul]; positivity
      · have ht' : 0 < |t| := abs_pos.mpr ht
        calc |t|⁻¹ * |f (x + t • v) - f x| ≤ |t|⁻¹ * (C * (|t| * ‖v‖)) := by gcongr
          _ = C * ‖v‖ := by field_simp
    · exact integrableOn_const (by rw [volume_cube]; exact ENNReal.one_ne_top)
    · filter_upwards [ae_restrict_of_ae hf.ae_differentiableAt] with x hx
      have h0 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      have hd : HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 :=
        hx.hasFDerivAt.comp_hasDerivAt_of_eq 0 h0 (by simp)
      have h2 := hasDerivAt_iff_tendsto_slope_zero.mp hd
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at h2
      exact ((Complex.continuous_ofReal.tendsto _).comp h2).const_mul _
  -- the translation moves onto `e_{−n}`
  have h2 : ∀ t : ℝ, A t = (t⁻¹ : ℂ) * (mFourier n (ofPi (t • v)) - 1) *
      cubeFourierCoeff (fun x => (f x : ℂ)) n := by
    intro t
    have hcont : ∀ w : ι → ℝ, Continuous fun x => mFourier (-n) (ofPi x) * (f (x + w) : ℂ) :=
      fun w => (continuous_mFourier_ofPi _).mul (Complex.continuous_ofReal.comp
        (hf.continuous.comp (continuous_id.add continuous_const)))
    have e1 : ∀ x, mFourier (-n) (ofPi x) * ((t⁻¹ * (f (x + t • v) - f x) : ℝ) : ℂ) =
        (t⁻¹ : ℂ) * (mFourier (-n) (ofPi x) * (f (x + t • v) : ℂ) -
          mFourier (-n) (ofPi x) * (f (x + 0) : ℂ)) := fun x => by
      push_cast; rw [add_zero]; ring
    have hF : IsPeriodic fun y => mFourier (-n) (ofPi (y + -(t • v))) * (f y : ℂ) := by
      intro y k
      simp only
      rw [show y + (fun i => (k i : ℝ)) + -(t • v) = (y + -(t • v)) + fun i => (k i : ℝ) by
        abel, ofPi_add_int, hper]
    have e2 : ∫ x in cube ι, mFourier (-n) (ofPi x) * (f (x + t • v) : ℂ) =
        mFourier n (ofPi (t • v)) * cubeFourierCoeff (fun x => (f x : ℂ)) n := by
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
  have h3 := (tendsto_slope_mFourier_ofPi_smul n v).mul_const
    (cubeFourierCoeff (fun x => (f x : ℂ)) n)
  exact tendsto_nhds_unique h1 (h3.congr fun t => (h2 t).symm)

end UnitAddTorus

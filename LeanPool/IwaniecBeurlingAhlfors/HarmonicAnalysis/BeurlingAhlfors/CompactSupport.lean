/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.CauchyTransform
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.CompactSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# `‖𝓑‖_p` as the best constant of `‖∂u‖_p ≤ C ‖∂_zbar u‖_p` on `C_c^∞`

For `1 < p < ∞` and `C ∈ [0, ∞]`, the norm of the Beurling–Ahlfors transform on `L^p (ℂ)` is at
most `C` if and only if `‖∂u‖_p ≤ C ‖∂_zbar u‖_p` for every smooth compactly supported `u : ℂ → ℂ`
(`HarmonicAnalysis.beurlingPowNorm_one_le_iff`): `‖𝓑‖_p` is the best constant of that inequality
(`HarmonicAnalysis.isLeast_beurlingPowNorm_one`). This is the reduction that
Baernstein–Montgomery-Smith state without proof (1999, §1, remark (b), and §2, (2.4)): the truth
of their Conjecture 3 (Iwaniec's), `∫ |∂_zbar f|^p ≤ (p* − 1)^p ∫ |∂f|^p` for `f ∈ W_hom^{1,p}`,
which holds
if and only if it holds with `∂f` and `∂_zbar f` interchanged, "would show that the norm of `S` on
`L^p (ℂ, ℂ)` is precisely `p* − 1`". They state the inequality on `W_hom^{1,p}`; here it is on
`C_c^∞`, which is what the reduction needs.

## Proof

Guerra's proof of Corollary 1.4 (A. Guerra, *Quasiconvexity of the Burkholder function on
symmetric matrices*, preprint, arXiv:2608.23388, 2026, §6), with the cut-offs of the proof of
Corollary 1.2 there:

1. **The dense class `C_c^∞`.** For `g ∈ C_c^∞`, let `f = C g` be its Cauchy transform,
   `f (z) = (1/π) ∫ g (w) / (z − w) dw`. Then `∂_zbar f = g`, `∂f = 𝓑 g`, `f = O (1/|z|)` and
   `∂f = O (1/|z|²)` (`HarmonicAnalysis.BeurlingAhlfors.CauchyTransform`).
2. **The cut-offs.** `η_R (z) = χ (z / R)`, `χ` a smooth bump function, `1` on the unit disc and
   `0` off the disc of radius `2`, so that `|Dη_R| ≤ K / R` and `Dη_R` vanishes off
   `R ≤ |z| ≤ 2R`. By the Leibniz rule `∂ (η_R f) − ∂f = (η_R − 1) ∂f + f ∂η_R`: the first term
   tends to `0` in `L^p` by dominated convergence (`∂f ∈ L^p`), and the second is at most
   `(A / R) (K / R)` on the disc of radius `2R` and `0` off it, so its `L^p` norm is at most
   `A K (4π)^{1/p} R^{2/p − 2} → 0`, since `p > 1`. The same holds for `∂_zbar`. So `∂ (η_R f) → 𝓑
   g`
   and `∂_zbar (η_R f) → g` in `L^p`
   (`HarmonicAnalysis.exists_hasCompactSupport_tendsto_cauchyTransform`), and the inequality
   for the `η_R f ∈ C_c^∞` gives `‖𝓑 g‖_p ≤ C ‖g‖_p`
   (`HarmonicAnalysis.eLpNorm_beurlingPow_one_le_of_hasCompactSupport`).
3. **Density.** `‖𝓑‖_p` is a supremum over the Schwartz functions `g`. The functions
   `g_n = η_n g ∈ C_c^∞` have `g_n → g` in `L^p` and `𝓕 g_n → 𝓕 g` in `L¹`
   (`HarmonicAnalysis.exists_hasCompactSupport_tendsto`), so `𝓑 g_n → 𝓑 g` uniformly
   (`HarmonicAnalysis.enorm_fourierMultiplier_sub_le`, `|(conj ξ)/ξ| ≤ 1`), and Fatou's lemma gives
   `‖𝓑 g‖_p ≤ liminf ‖𝓑 g_n‖_p ≤ C ‖g‖_p`.

**The one departure from Guerra's proof, which is forced.** Guerra treats the Hessian case: a
real `h ∈ C_c^∞`, its logarithmic potential `u = (1/π) ∫ log |x − y| h (y) dy`, and the parts
`a₊ = h`, `a₋ = conj (𝒮 h)` of `D²u`. The norm of `𝓑` on complex `L^p`, and the inequality for
`∂u`, `∂_zbar u` of complex `u` from which it is derived here, are the gradient case: a complex
`g ∈ C_c^∞` and its Cauchy transform `f`, with `∂_zbar f = g` and `∂f = 𝓑 g`, in place of `h` and
`u`.
The steps of the proof are Guerra's, with the decay `f = O (1/|z|)`, `∂f = O (1/|z|²)` in place of
`Du = O (|x|^{−1})`, `D²u = O (|x|^{−2})`.

**Guerra's "by density".** Guerra passes from `C_c^∞` to `L^p` "by density", which presupposes
that `𝒮` is bounded on `L^p`. The library does not prove that boundedness (a theorem of
Calderón–Zygmund theory) and does not need it: step 3 passes to the limit by Fatou's lemma, with
the convergence of the Fourier transforms in `L¹`.

The converse is `𝓑 (∂_zbar u) = ∂u` (`HarmonicAnalysis.beurlingPow_dzbarCLM_pow`) and the definition
of `‖𝓑‖_p`.

## References

* A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and
  `∂_zbar f`*, in: Complex analysis and differential equations (Uppsala, 1997), ed. C. Kiselman,
  Acta
  Univ. Upsaliensis C 64 (1999), 92–109, [arXiv:math/9709215](https://arxiv.org/abs/math/9709215),
  §1, Conjecture 3 and remark (b); §2, (2.4).
* A. Guerra, *Quasiconvexity of the Burkholder function on symmetric matrices*, preprint,
  [arXiv:2608.23388](https://arxiv.org/abs/2608.23388) (2026), §6: the proofs of Corollaries 1.2
  and 1.4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped SchwartzMap FourierTransform ENNReal ContDiff Real

namespace HarmonicAnalysis

/-! ### Cut-offs -/

/-- `½ (∂_x g + s ∂_y g)`: `∂g` for `s = −i`, `∂_zbar g` for `s = i`. -/
private def wirt (s : ℂ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  2⁻¹ * (fderiv ℝ g z 1 + s * fderiv ℝ g z Complex.I)

/-- `∂ = wirt (−i)`. -/
private lemma dz_eq_wirt (g : ℂ → ℂ) : dz g = wirt (-Complex.I) g := by
  funext z
  simp only [dz, wirt, smul_eq_mul, neg_mul, sub_eq_add_neg]

/-- `∂_zbar = wirt i`. -/
private lemma dzbar_eq_wirt (g : ℂ → ℂ) : dzbar g = wirt Complex.I g := by
  funext z
  simp only [dzbar, wirt, smul_eq_mul]

/-- `wirt s g` is measurable for every `g`. -/
private lemma measurable_wirt (s : ℂ) (g : ℂ → ℂ) : Measurable (wirt s g) := by
  unfold wirt
  fun_prop

/-- The Leibniz rule `D (c d) = c D d + d D c`. -/
private lemma wirt_mul (s : ℂ) {c d : ℂ → ℂ} {z : ℂ} (hc : DifferentiableAt ℝ c z)
    (hd : DifferentiableAt ℝ d z) :
    wirt s (fun w => c w * d w) z = c z * wirt s d z + d z * wirt s c z := by
  simp only [wirt, fderiv_fun_mul hc hd, add_apply, smul_apply, smul_eq_mul]
  ring

/-- The chain rule for a dilation: `D (ψ (r ·)) (z) = r D ψ (r z)`. -/
private lemma wirt_comp_smul (s : ℂ) (ψ : ℂ → ℂ) (r : ℝ) (z : ℂ) :
    wirt s (fun w => ψ (r • w)) z = r * wirt s ψ (r • z) := by
  have h : fderiv ℝ (fun w => ψ (r • w)) z = r • fderiv ℝ ψ (r • z) := fderiv_comp_smul r
  unfold wirt
  rw [h]
  simp only [smul_apply, Complex.real_smul]
  ring

/-- The bump function `χ`: `1` on the closed unit disc, `0` off the disc of radius `2`. -/
private def bump : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cut-off `η_R (z) = χ (z / R)`. -/
private def cutoff (R : ℝ) (z : ℂ) : ℂ := (bump (R⁻¹ • z) : ℂ)

/-- `η_R` is smooth. -/
private lemma contDiff_cutoff (R : ℝ) : ContDiff ℝ ∞ (cutoff R) :=
  (Complex.ofRealCLM.contDiff.comp bump.contDiff).comp (contDiff_const_smul R⁻¹)

/-- `η_R` has compact support. -/
private lemma hasCompactSupport_cutoff {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (cutoff R) :=
  (bump.hasCompactSupport.comp_left Complex.ofReal_zero).comp_smul (inv_ne_zero hR)

/-- `η_R = 1` on the closed disc of radius `R`. -/
private lemma cutoff_eq_one {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) : cutoff R z = 1 := by
  rw [cutoff, bump.one_of_mem_closedBall, Complex.ofReal_one]
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
    inv_mul_le_iff₀ hR]
  change ‖z‖ ≤ R * 1
  rwa [mul_one]

/-- `|η_R − 1| ≤ 1`, since `0 ≤ η_R ≤ 1`. -/
private lemma norm_cutoff_sub_one_le (R : ℝ) (z : ℂ) : ‖cutoff R z - 1‖ ≤ 1 := by
  rw [cutoff, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_le]
  constructor <;> linarith [bump.nonneg (x := R⁻¹ • z), bump.le_one (x := R⁻¹ • z)]

/-- `|∂η_R|, |∂_zbar η_R| ≤ K / R`, `K` a bound of `|∂χ|`, `|∂_zbar χ|`. -/
private lemma exists_norm_wirt_cutoff_le (s : ℂ) :
    ∃ K, ∀ R : ℝ, 0 < R → ∀ z, ‖wirt s (cutoff R) z‖ ≤ R⁻¹ * K := by
  set ψ : ℂ → ℂ := fun z => (bump z : ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp bump.contDiff
  have hcont : Continuous (wirt s ψ) := by
    have := hψ.continuous_fderiv (by simp)
    unfold wirt
    fun_prop
  have hsupp : HasCompactSupport (wirt s ψ) := by
    refine ((bump.hasCompactSupport.comp_left Complex.ofReal_zero).fderiv (𝕜 := ℝ)).mono ?_
    intro z hz
    rw [Function.mem_support] at hz ⊢
    contrapose hz
    have h0 : fderiv ℝ ψ z = 0 := hz
    simp [wirt, h0]
  obtain ⟨K, hK⟩ := hcont.bounded_above_of_compact_support hsupp
  refine ⟨K, fun R hR z => ?_⟩
  have h : cutoff R = fun w => ψ (R⁻¹ • w) := rfl
  rw [h, wirt_comp_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  exact mul_le_mul_of_nonneg_left (hK _) (inv_nonneg.2 hR.le)

/-- Dominated convergence in `L^p`, `0 < p < ∞`: if `|c_n| ≤ 1`, `c_n (z) = 0` for large `n` and
`h ∈ L^p`, then `‖c_n h‖_p → 0`. -/
private lemma tendsto_eLpNorm_mul_of_eventually_zero {c : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {p : ℝ}
    (hp : 0 < p) (hc : ∀ n, Continuous (c n)) (hcb : ∀ n z, ‖c n z‖ ≤ 1)
    (hlim : ∀ z, ∀ᶠ n in atTop, c n z = 0) (hh : MemLp h (ENNReal.ofReal p) volume) :
    Tendsto (fun n => eLpNorm (fun z => c n z * h z) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hmeas : ∀ n, AEStronglyMeasurable (fun z => c n z * h z) volume := fun n =>
    (hc n).aestronglyMeasurable.mul hh.aestronglyMeasurable
  have hint : Tendsto (fun n => ∫⁻ z, ‖c n z * h z‖ₑ ^ p) atTop (𝓝 (∫⁻ _ : ℂ, 0)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun z => ‖h z‖ₑ ^ p)
      (fun n => (hmeas n).eNorm.pow_const p) (fun n => ae_of_all _ fun z => ?_) ?_
      (ae_of_all _ fun z => ?_)
    · refine ENNReal.rpow_le_rpow ?_ hp.le
      rw [eNorm_mul]
      calc ‖c n z‖ₑ * ‖h z‖ₑ ≤ 1 * ‖h z‖ₑ := by
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_one.2 (hcb n z)
        _ = ‖h z‖ₑ := one_mul _
    · rw [← eLpNorm_ofReal_rpow_eq_lintegral hp hh.aestronglyMeasurable]
      exact ENNReal.rpow_ne_top_of_nonneg hp.le hh.eLpNorm_lt_top.ne
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim z] with n hn
      simp [hn, ENNReal.zero_rpow_of_pos hp]
  rw [lintegral_zero] at hint
  have h1 := hint.ennrpow_const (1 / p)
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at h1
  refine h1.congr fun n => ?_
  rw [← eLpNorm_ofReal_rpow_eq_lintegral hp (hmeas n), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- `D η_R (z) = 0` where `η_R` is locally constant: for `|z| < R` (`η_R = 1`) and for `|z| > 2R`
(`η_R = 0`). -/
private lemma wirt_cutoff_eq_zero (s : ℂ) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : ‖z‖ < R ∨ 2 * R < ‖z‖) : wirt s (cutoff R) z = 0 := by
  have h : ∃ c : ℂ, cutoff R =ᶠ[𝓝 z] fun _ => c := by
    rcases hz with hz | hz
    · refine ⟨1, ?_⟩
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
      exact cutoff_eq_one hR hw.le
    · refine ⟨0, ?_⟩
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
      have hw' : 2 * R < ‖w‖ := hw
      rw [cutoff, bump.zero_of_le_dist, Complex.ofReal_zero]
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
      change 2 ≤ R⁻¹ * ‖w‖
      rw [le_inv_mul_iff₀ hR]
      linarith
  obtain ⟨c, hc⟩ := h
  simp [wirt, hc.fderiv_eq]

/-- `‖f Dη_R‖_p → 0` as `R → ∞` (`R = n + 1`) if `|f (z)| ≤ A / |z|` for `|z| ≥ R₀` and `1 < p`:
`f Dη_R` is at most `(A / R) (K / R)` on the disc of radius `2R` and `0` off it, so
`‖f Dη_R‖_p ≤ A K (4π)^{1/p} R^{2/p − 2}`. -/
private lemma tendsto_eLpNorm_mul_wirt_cutoff (s : ℂ) {f : ℂ → ℂ} (hf : Continuous f)
    {A R₀ : ℝ} (hR₀ : 0 < R₀) (hdecay : ∀ z, R₀ ≤ ‖z‖ → ‖f z‖ ≤ A / ‖z‖) {p : ℝ} (hp : 1 < p) :
    Tendsto (fun n : ℕ => eLpNorm (fun z => f z * wirt s (cutoff ((n : ℝ) + 1)) z)
      (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨K, hK⟩ := exists_norm_wirt_cutoff_le s
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg _).trans (hK 1 one_pos 0)
    simpa using this
  have hA0 : 0 ≤ A := by
    have h1 := (norm_nonneg _).trans (hdecay (R₀ : ℂ) (by simp [abs_of_pos hR₀]))
    rw [Complex.norm_real, Real.norm_of_nonneg hR₀.le, le_div_iff₀ hR₀, zero_mul] at h1
    exact h1
  set c : ℝ := A * K * (4 * π) ^ (1 / p)
  set e : ℝ := 2 - 2 / p
  have he : 0 < e := by
    have : 2 / p < 2 := by rw [div_lt_iff₀ hp0]; linarith
    simp only [e]; linarith
  -- the bound for `R ≥ R₀`
  have hbound : ∀ R : ℝ, R₀ ≤ R → eLpNorm (fun z => f z * wirt s (cutoff R) z)
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (c * R ^ (-e)) := by
    intro R hR
    have hR0 : 0 < R := hR₀.trans_le hR
    have hpt : ∀ z, ‖f z * wirt s (cutoff R) z‖ ≤
        (closedBall (0 : ℂ) (2 * R)).indicator (fun _ => A * K / R ^ 2) z := by
      intro z
      by_cases hw : wirt s (cutoff R) z = 0
      · rw [hw, mul_zero, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by positivity) z
      · have h1 : R ≤ ‖z‖ := by
          by_contra h
          exact hw (wirt_cutoff_eq_zero s hR0 (Or.inl (not_le.1 h)))
        have h2 : ‖z‖ ≤ 2 * R := by
          by_contra h
          exact hw (wirt_cutoff_eq_zero s hR0 (Or.inr (not_le.1 h)))
        rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 h2), norm_mul]
        calc ‖f z‖ * ‖wirt s (cutoff R) z‖ ≤ (A / R) * (R⁻¹ * K) := by
              gcongr
              · exact (hdecay z (hR.trans h1)).trans (div_le_div_of_nonneg_left hA0 hR0 h1)
              · exact hK R hR0 z
          _ = A * K / R ^ 2 := by field_simp
    have hmono := eLpNorm_mono_real (μ := volume) (p := ENNReal.ofReal p)
      (hf.aestronglyMeasurable.mul (measurable_wirt s _).aestronglyMeasurable) hpt
    rw [eLpNorm_indicator_const (measurableSet_closedBall (α := ℂ) (x := 0)
      (ε := 2 * R)).nullMeasurableSet (by simpa using hp0)
      ENNReal.ofReal_ne_top, Complex.volume_closedBall, ENNReal.toReal_ofReal hp0.le] at hmono
    refine hmono.trans (le_of_eq ?_)
    have hπ : ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal π := by
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
    rw [hπ, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      Real.eNorm_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : ((2 * R) ^ 2 * π) ^ (1 / p) = (4 * π) ^ (1 / p) * R ^ (2 / p) := by
      rw [show (2 * R) ^ 2 * π = (4 * π) * R ^ 2 by ring, Real.mul_rpow (by positivity)
        (by positivity), ← Real.rpow_natCast R 2, ← Real.rpow_mul hR0.le, Nat.cast_ofNat,
        mul_one_div]
    have h2 : R ^ (-e) = R ^ (2 / p) / R ^ 2 := by
      rw [Real.rpow_neg hR0.le, Real.rpow_sub hR0, Real.rpow_two, inv_div]
    rw [h1, h2]
    simp only [c]
    field_simp
  -- the bound tends to `0`
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (c * ((n : ℝ) + 1) ^ (-e))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 := ((tendsto_rpow_neg_atTop he).comp h1).const_mul c
    rw [mul_zero] at h2
    simpa using ENNReal.tendsto_ofReal h2
  obtain ⟨N, hN⟩ := exists_nat_ge R₀
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  refine hbound _ ?_
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- For `u_n = η_{n+1} f`, `f` smooth with `|f (z)| ≤ A / |z|` for `|z| ≥ R₀`, `1 < p`:
`‖∂u_n − ∂f‖_p → 0` if `∂f ∈ L^p`, and `‖∂_zbar u_n − ∂_zbar f‖_p → 0` if `∂_zbar f ∈ L^p` (`s =
∓i`). -/
private lemma tendsto_wirt_cutoff_mul (s : ℂ) {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) {A R₀ : ℝ}
    (hR₀ : 0 < R₀) (hdecay : ∀ z, R₀ ≤ ‖z‖ → ‖f z‖ ≤ A / ‖z‖) {p : ℝ} (hp : 1 < p)
    (hwf : MemLp (wirt s f) (ENNReal.ofReal p) volume) :
    Tendsto (fun n : ℕ => eLpNorm (fun z => wirt s (fun w => cutoff ((n : ℝ) + 1) w * f w) z -
      wirt s f z) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  set P := ENNReal.ofReal p
  have hR : ∀ n : ℕ, (0 : ℝ) < n + 1 := fun n => by positivity
  -- `(η_R − 1) ∂f → 0`, by dominated convergence
  have h1 : Tendsto (fun n : ℕ => eLpNorm (fun z => (cutoff ((n : ℝ) + 1) z - 1) * wirt s f z) P
      volume) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_mul_of_eventually_zero (by linarith)
      (fun n => (contDiff_cutoff _).continuous.sub continuous_const)
      (fun n z => norm_cutoff_sub_one_le _ _) (fun z => ?_) hwf
    obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [cutoff_eq_one (hR n), sub_self]
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- `f ∂η_R → 0`
  have h2 := tendsto_eLpNorm_mul_wirt_cutoff s hf.continuous hR₀ hdecay hp
  -- `∂u_R − ∂f = (η_R − 1) ∂f + f ∂η_R`
  have hlim := ENNReal.Tendsto.const_mul (h1.add h2) (Or.inr (ENNReal.LpAddConst_lt_top P).ne)
  rw [add_zero, mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => le_of_eq_of_le ?_ (eLpNorm_add_le' P)
  congr 1
  funext z
  rw [wirt_mul s ((contDiff_cutoff _).contDiffAt.differentiableAt (by simp))
    (hf.differentiable (by simp) z)]
  simp only [Pi.add_apply]
  ring

/-- **Cut-offs of the Cauchy transform** (Guerra's step "`D (η_R u) → Du` in `L^p`", in the
gradient case). For `g ∈ C_c^∞` and `1 < p`, the smooth compactly supported `u_n = η_{n+1} C g`
have `∂u_n → ∂ (C g) = 𝓑 g` and `∂_zbar u_n → ∂_zbar (C g) = g` in `L^p`. -/
theorem exists_hasCompactSupport_tendsto_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) {p : ℝ} (hp : 1 < p) :
    ∃ u : ℕ → ℂ → ℂ, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      Tendsto (fun n => eLpNorm (fun z => dz (u n) z - beurlingPow 1 g z) (ENNReal.ofReal p)
        volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => dzbar (u n) z - g z) (ENNReal.ofReal p) volume)
        atTop (𝓝 0) := by
  set f := cauchyTransform g
  have hf : ContDiff ℝ ∞ f := contDiff_cauchyTransform hg hgc
  obtain ⟨A, R₀, hR₀, hdecay⟩ := exists_norm_cauchyTransform_le hg.continuous hgc
  refine ⟨fun n w => cutoff ((n : ℝ) + 1) w * f w, fun n => (contDiff_cutoff _).mul hf,
    fun n => (hasCompactSupport_cutoff (by positivity)).mul_right, ?_, ?_⟩
  · have hw : MemLp (wirt (-Complex.I) f) (ENNReal.ofReal p) volume := by
      rw [← dz_eq_wirt]
      exact memLp_dz_cauchyTransform hg hgc hp
    refine (tendsto_wirt_cutoff_mul _ hf hR₀ hdecay hp hw).congr fun n => ?_
    congr 1
    funext z
    rw [← dz_eq_wirt, ← dz_eq_wirt, show dz f = beurlingPow 1 g from
      dz_cauchyTransform_eq_beurlingPow_one hg hgc]
  · have hw : MemLp (wirt Complex.I f) (ENNReal.ofReal p) volume := by
      rw [← dzbar_eq_wirt, show dzbar f = g from dzbar_cauchyTransform_eq hg hgc]
      exact hg.continuous.memLp_of_hasCompactSupport hgc
    refine (tendsto_wirt_cutoff_mul _ hf hR₀ hdecay hp hw).congr fun n => ?_
    congr 1
    funext z
    rw [← dzbar_eq_wirt, ← dzbar_eq_wirt, show dzbar f = g from dzbar_cauchyTransform_eq hg hgc]

/-- `𝓑 0 = 0`. -/
private lemma beurlingPow_one_zero : beurlingPow 1 (0 : ℂ → ℂ) = 0 := by
  funext z
  simp [beurlingPow, fourierMultiplier, Real.fourier_eq, Real.fourierInv_eq]

/-- **The dense class `C_c^∞`** (Guerra, 2026, preprint, proof of Corollary 1.4, in the gradient
case): if `‖∂u‖_p ≤ C ‖∂_zbar u‖_p` for every smooth compactly supported `u`, `1 < p < ∞`, then
`‖𝓑 g‖_p ≤ C ‖g‖_p` for every smooth compactly supported `g`: apply the inequality to the
`η_R C g` of `HarmonicAnalysis.exists_hasCompactSupport_tendsto_cauchyTransform` and let
`R → ∞`. -/
theorem eLpNorm_beurlingPow_one_le_of_hasCompactSupport {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (h : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume)
    {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    eLpNorm (beurlingPow 1 g) (ENNReal.ofReal p) volume ≤
      C * eLpNorm g (ENNReal.ofReal p) volume := by
  set P := ENNReal.ofReal p
  have hP : 1 ≤ P := by simpa [P] using ENNReal.ofReal_le_ofReal hp.le
  have hP0 : P ≠ 0 := (zero_lt_one.trans_le hP).ne'
  rcases eq_or_ne C ⊤ with rfl | hC
  · by_cases h0 : eLpNorm g P volume = 0
    · -- `g = 0`, hence `𝓑 g = 0`
      have hz : g = 0 := by
        rw [eLpNorm_eq_zero_iff hP0] at h0
        exact (hg.continuous.ae_eq_iff_eq volume continuous_zero).1 h0
      simp [hz, beurlingPow_one_zero]
    · rw [ENNReal.top_mul h0]
      exact le_top
  · obtain ⟨u, hu, huc, hdz, hdzbar⟩ := exists_hasCompactSupport_tendsto_cauchyTransform hg hgc hp
    have hlim : Tendsto (fun n => eLpNorm (fun z => dz (u n) z - beurlingPow 1 g z) P volume +
        C * (eLpNorm (fun z => dzbar (u n) z - g z) P volume + eLpNorm g P volume)) atTop
        (𝓝 (C * eLpNorm g P volume)) := by
      simpa using hdz.add (ENNReal.Tendsto.const_mul (hdzbar.add_const _) (Or.inr hC))
    refine ge_of_tendsto' hlim fun n => ?_
    calc eLpNorm (beurlingPow 1 g) P volume
        ≤ eLpNorm (fun z => dz (u n) z - beurlingPow 1 g z) P volume +
            eLpNorm (dz (u n)) P volume := by
          have e := eLpNorm_sub_le (μ := volume) (f := dz (u n))
            (g := fun z => dz (u n) z - beurlingPow 1 g z) hP
          rw [add_comm]
          convert e using 2
          funext z
          simp
      _ ≤ eLpNorm (fun z => dz (u n) z - beurlingPow 1 g z) P volume +
          C * eLpNorm (dzbar (u n)) P volume := by
          gcongr
          exact h _ (hu n) (huc n)
      _ ≤ _ := by
          gcongr
          have e := eLpNorm_add_le (μ := volume) (f := fun z => dzbar (u n) z - g z) (g := g) hP
          convert e using 2
          funext z
          simp

/-! ### Density -/

/-- The step from `C_c^∞` to all Schwartz functions, for `C < ∞` (Guerra's "by density"): the
`g_n = η_n g ∈ C_c^∞` of `HarmonicAnalysis.exists_hasCompactSupport_tendsto` have `g_n → g` in
`L^p` and `𝓕 g_n → 𝓕 g` in `L¹`, hence `𝓑 g_n → 𝓑 g` pointwise, and Fatou's lemma gives
`‖𝓑 g‖_p ≤ liminf ‖𝓑 g_n‖_p ≤ C ‖g‖_p`. -/
private theorem eLpNorm_beurlingPow_one_le_of_ne_top {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : C ≠ ⊤)
    (h : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume)
    (g : 𝓢(ℂ, ℂ)) :
    eLpNorm (beurlingPow 1 g) (ENNReal.ofReal p) volume ≤
      C * eLpNorm g (ENNReal.ofReal p) volume := by
  set P := ENNReal.ofReal p
  have hP : 1 ≤ P := by simpa [P] using ENNReal.ofReal_le_ofReal hp.le
  obtain ⟨φ, hφ, hφp, hφ1⟩ := exists_hasCompactSupport_tendsto g
  have hm : Measurable fun ξ => beurlingSymbol ξ ^ 1 := measurable_beurlingSymbol.pow_const 1
  have hm1 : ∀ ξ, ‖beurlingSymbol ξ ^ 1‖ ≤ 1 := fun ξ => by
    simpa using norm_beurlingSymbol_le ξ
  -- `𝓑 φ_j → 𝓑 g` pointwise (uniformly), since `𝓕 φ_j → 𝓕 g` in `L¹`
  have hlim : ∀ x, Tendsto (fun j => beurlingPow 1 (φ j) x) atTop (𝓝 (beurlingPow 1 g x)) := by
    intro x
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hφ1 (fun _ => zero_le)
      fun j => ?_
    rw [eDist_eq_eNorm_sub]
    exact enorm_fourierMultiplier_sub_le hm hm1 (φ j) g x
  -- Fatou's lemma
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := P) (μ := volume)
    (fun j => (continuous_fourierMultiplier _ (φ j)).aestronglyMeasurable) (beurlingPow 1 g)
    (continuous_fourierMultiplier _ g).aestronglyMeasurable (ae_of_all _ hlim)
  have hbound : ∀ j, eLpNorm (beurlingPow 1 (φ j)) P volume ≤
      C * (eLpNorm (fun x => φ j x - g x) P volume + eLpNorm g P volume) := fun j => by
    refine (eLpNorm_beurlingPow_one_le_of_hasCompactSupport hp h ((φ j).smooth ⊤)
      (hφ j)).trans ?_
    gcongr
    have e := eLpNorm_add_le (μ := volume) (f := fun x => φ j x - g x) (g := g) hP
    convert e using 2
    funext x
    simp
  have hlim2 : Tendsto (fun j => C * (eLpNorm (fun x => φ j x - g x) P volume +
      eLpNorm g P volume)) atTop (𝓝 (C * eLpNorm g P volume)) := by
    simpa using ENNReal.Tendsto.const_mul ((hφp p hp.le).add_const _) (Or.inr hC)
  calc eLpNorm (beurlingPow 1 g) P volume
      ≤ atTop.liminf fun j => eLpNorm (beurlingPow 1 (φ j)) P volume := hfatou
    _ ≤ atTop.liminf fun j => C * (eLpNorm (fun x => φ j x - g x) P volume +
          eLpNorm g P volume) := liminf_le_liminf (Eventually.of_forall hbound)
    _ = C * eLpNorm g P volume := hlim2.liminf_eq

/-! ### The norm of `𝓑` -/

/-- **The norm of `𝓑` on `L^p` is at most the constant of `‖∂u‖_p ≤ C ‖∂_zbar u‖_p` on `C_c^∞`**,
`1 < p < ∞`: if `‖∂u‖_p ≤ C ‖∂_zbar u‖_p` for every smooth compactly supported `u`, then
`‖𝓑‖_p ≤ C`. Baernstein–Montgomery-Smith state it without proof (1999, §1, remark (b): their
Conjecture 3 "would show that the norm of `S` on `L^p (ℂ, ℂ)` is precisely `p* − 1`"). The proof
is Guerra's proof of Corollary 1.4 (2026, preprint) in the gradient case: the dense class
`C_c^∞`, the Cauchy transform as the potential, the cut-offs `η_R`, the limit `R → ∞`, and
density (see the module docstring). -/
theorem beurlingPowNorm_one_le_of_forall_hasCompactSupport {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (h : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume) :
    beurlingPowNorm 1 p ≤ C := by
  rcases eq_or_ne C ⊤ with rfl | hC
  · exact le_top
  exact iSup_le fun g => ENNReal.div_le_of_le_mul (eLpNorm_beurlingPow_one_le_of_ne_top hp hC h g)

/-- `‖𝓑 g‖_p ≤ C ‖g‖_p` for every Schwartz function `g` if `‖∂u‖_p ≤ C ‖∂_zbar u‖_p` for every
smooth
compactly supported `u`, `1 < p < ∞`: `‖𝓑 g‖_p ≤ ‖𝓑‖_p ‖g‖_p` and
`HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport`. -/
theorem eLpNorm_beurlingPow_one_le_of_forall_hasCompactSupport {p : ℝ} (hp : 1 < p)
    {C : ℝ≥0∞}
    (h : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume)
    (g : 𝓢(ℂ, ℂ)) :
    eLpNorm (beurlingPow 1 g) (ENNReal.ofReal p) volume ≤
      C * eLpNorm g (ENNReal.ofReal p) volume :=
  (eLpNorm_fourierMultiplier_le _ p g).trans
    (mul_le_mul_left (beurlingPowNorm_one_le_of_forall_hasCompactSupport hp h) _)

/-- **The converse**: `‖∂u‖_p ≤ ‖𝓑‖_p ‖∂_zbar u‖_p` for every smooth compactly supported `u`, since
`u` is a Schwartz function and `𝓑 (∂_zbar u) = ∂u` (`HarmonicAnalysis.beurlingPow_dzbarCLM_pow`). -/
theorem eLpNorm_dz_le_beurlingPowNorm_one_mul (p : ℝ) {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) :
    eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
      beurlingPowNorm 1 p * eLpNorm (dzbar u) (ENNReal.ofReal p) volume := by
  set U : 𝓢(ℂ, ℂ) := huc.toSchwartzMap hu
  have hU : (U : ℂ → ℂ) = u := rfl
  have h1 : dz u = dzCLM U := by
    rw [← hU]
    exact funext fun z => (dzCLM_apply U z).symm
  have h2 : dzbar u = dzbarCLM U := by
    rw [← hU]
    exact funext fun z => (dzbarCLM_apply U z).symm
  have h3 := beurlingPow_dzbarCLM_pow 1 U
  simp only [pow_one] at h3
  rw [h1, h2, ← h3]
  exact eLpNorm_fourierMultiplier_le _ p (dzbarCLM U)

/-- **`‖𝓑‖_p` is the best constant of `‖∂u‖_p ≤ C ‖∂_zbar u‖_p` on `C_c^∞`**, `1 < p < ∞`:
`‖𝓑‖_p ≤ C` if and only if `‖∂u‖_p ≤ C ‖∂_zbar u‖_p` for every smooth compactly supported `u`.
This is
the reduction of Baernstein–Montgomery-Smith (1999, §1, remark (b), stated without proof), by
`HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport` (Guerra's argument) and
the converse `HarmonicAnalysis.eLpNorm_dz_le_beurlingPowNorm_one_mul`. -/
theorem beurlingPowNorm_one_le_iff {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞} :
    beurlingPowNorm 1 p ≤ C ↔ ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume :=
  ⟨fun hC _ hu huc => (eLpNorm_dz_le_beurlingPowNorm_one_mul p hu huc).trans
    (mul_le_mul_left hC _), beurlingPowNorm_one_le_of_forall_hasCompactSupport hp⟩

/-- `‖𝓑‖_p` is the least `C ∈ [0, ∞]` with `‖∂u‖_p ≤ C ‖∂_zbar u‖_p` for all `u ∈ C_c^∞`,
`1 < p < ∞` (`HarmonicAnalysis.beurlingPowNorm_one_le_iff`). -/
theorem isLeast_beurlingPowNorm_one {p : ℝ} (hp : 1 < p) :
    IsLeast {C : ℝ≥0∞ | ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume} (beurlingPowNorm 1 p) :=
  ⟨(beurlingPowNorm_one_le_iff hp).1 le_rfl, fun _ hC => (beurlingPowNorm_one_le_iff hp).2 hC⟩

end HarmonicAnalysis

/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Density
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Density of the compactly supported Schwartz functions, by cut-offs

`V` is a finite-dimensional real inner product space with its Lebesgue measure.
`HarmonicAnalysis.exists_hasCompactSupport_tendsto` is the density of `C_c^∞ (V)` in the Schwartz
space `𝓢 (V)` in the two senses used with Fourier multipliers: for every Schwartz function `f`
there are compactly supported Schwartz functions `φ_n` such that `φ_n → f` in `L^p` for every
`1 ≤ p < ∞`, and `𝓕 φ_n → 𝓕 f` in `L^1`.

## Proof

By cut-offs: `φ_n (x) = η (x / (n + 1)) f (x)`, where `η` is a smooth bump function (a
`ContDiffBump`, even, with values in `[0, 1]`) equal to `1` on the unit ball.

* `φ_n → f` in `L^p` by dominated convergence: `|φ_n − f| ≤ |f|`, and `φ_n (x) = f (x)` as soon as
  `|x| ≤ n + 1`.
* On the Fourier side, `𝓕 φ_n = ψ_{1/(n+1)} ∗ 𝓕 f` is a mollification of `𝓕 f`
  (`HarmonicAnalysis.mollify`), where `𝓕 ψ = η` and `∫ ψ = η (0) = 1`: both sides have Fourier
  transform `ξ ↦ η (ξ / (n + 1)) f (−ξ)`, since `𝓕 (𝓕 u) = u (−·)` and `η` is even. Then
  `𝓕 φ_n → 𝓕 f` in `L^1` is `HarmonicAnalysis.tendsto_eLpNorm_mollify_sub` with `p = 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform ENNReal ContDiff

namespace HarmonicAnalysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- `𝓕 (𝓕 u) (ξ) = u (−ξ)` for a Schwartz function `u`. -/
private lemma fourier_fourier_apply (u : 𝓢(V, ℂ)) (ξ : V) : 𝓕 (𝓕 u) ξ = u (-ξ) := by
  have h := Real.fourierInv_eq_fourier_neg (𝓕 (u : V → ℂ)) (-ξ)
  rw [neg_neg] at h
  have hinv : 𝓕⁻ (𝓕 u) = u := FourierTransform.fourierInv_fourier_eq u
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, ← h, ← SchwartzMap.fourier_coe,
    ← SchwartzMap.fourierInv_coe, hinv]

/-- **Density of `C_c^∞` in the Schwartz space, by cut-offs**: for every Schwartz function `f` there
are compactly supported Schwartz functions `φ_n` such that `φ_n → f` in `L^p` for every
`1 ≤ p < ∞`, and `𝓕 φ_n → 𝓕 f` in `L^1`. They are `φ_n (x) = η (x / (n + 1)) f (x)`, `η` a bump
function equal to `1` near `0`. -/
theorem exists_hasCompactSupport_tendsto (f : 𝓢(V, ℂ)) :
    ∃ φ : ℕ → 𝓢(V, ℂ), (∀ n, HasCompactSupport (φ n)) ∧
      (∀ p : ℝ, 1 ≤ p → Tendsto (fun n => eLpNorm (fun x => φ n x - f x) (ENNReal.ofReal p) volume)
        atTop (𝓝 0)) ∧
      Tendsto (fun n => eLpNorm (fun ξ => 𝓕 (φ n) ξ - 𝓕 f ξ) 1 volume) atTop (𝓝 0) := by
  -- the cut-off `η`, a bump function equal to `1` on the unit ball, as a Schwartz function `X`
  let χ : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have hχc : HasCompactSupport fun ξ => (χ ξ : ℂ) :=
    χ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hχs : ContDiff ℝ ∞ fun ξ => (χ ξ : ℂ) := Complex.ofRealCLM.contDiff.comp χ.contDiff
  let X : 𝓢(V, ℂ) := hχc.toSchwartzMap hχs
  have hX : ∀ ξ, X ξ = χ ξ := fun _ => rfl
  -- `t_n = 1 / (n + 1)` and `φ_n (x) = η (t_n x) f (x)`
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht0 : ∀ n, t n ≠ 0 := fun n => by positivity
  have hg : ∀ n, (fun x : V => X (t n • x)).HasTemperateGrowth := fun n =>
    X.hasTemperateGrowth.comp (by fun_prop : (fun x : V => t n • x).HasTemperateGrowth)
  set φ : ℕ → 𝓢(V, ℂ) := fun n => SchwartzMap.smulLeftCLM ℂ (fun x => X (t n • x)) f
  have hφ : ∀ n x, φ n x = χ (t n • x) * f x := fun n x => by
    rw [SchwartzMap.smulLeftCLM_apply_apply (hg n), hX, smul_eq_mul]
  -- `ψ` with `𝓕 ψ = X`, so that `∫ ψ = η (0) = 1`
  set ψ : 𝓢(V, ℂ) := 𝓕⁻ X
  have hψX : 𝓕 ψ = X := FourierTransform.fourier_fourierInv_eq X
  have hψ : ∫ y, ψ y = 1 := by
    have h : 𝓕 ψ 0 = 1 := by
      rw [hψX, hX, χ.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one),
        Complex.ofReal_one]
    rw [SchwartzMap.fourier_coe, Real.fourier_eq] at h
    simpa using h
  -- `𝓕 φ_n = ψ_{t_n} ∗ 𝓕 f`: both have Fourier transform `ξ ↦ η (t_n ξ) f (−ξ)`
  have hFφ : ∀ n, 𝓕 (φ n) = mollify ψ (𝓕 f) (t n) := fun n => by
    have key : 𝓕 (𝓕 (φ n)) = 𝓕 (mollify ψ (𝓕 f) (t n)) := by
      ext ξ
      rw [fourier_fourier_apply, fourier_mollify, fourier_fourier_apply, hψX, hX, hφ, smul_neg,
        χ.neg]
    calc 𝓕 (φ n) = 𝓕⁻ (𝓕 (𝓕 (φ n))) := (FourierTransform.fourierInv_fourier_eq _).symm
      _ = 𝓕⁻ (𝓕 (mollify ψ (𝓕 f) (t n))) := by rw [key]
      _ = mollify ψ (𝓕 f) (t n) := FourierTransform.fourierInv_fourier_eq _
  refine ⟨φ, fun n => ?_, fun p hp => ?_, ?_⟩
  · -- compact support
    have h : (φ n : V → ℂ) = (fun x => (χ (t n • x) : ℂ)) * (f : V → ℂ) := funext (hφ n)
    rw [h]
    exact (hχc.comp_smul (ht0 n)).mul_right
  · -- `φ_n → f` in `L^p`, by dominated convergence
    have hp0 : 0 < p := by linarith
    have hP0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
    have heq : ∀ g : V → ℂ, Continuous g →
        eLpNorm g (ENNReal.ofReal p) volume = (∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 / p) := fun g hg => by
      rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hP0 ENNReal.ofReal_ne_top
        hg.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
    have hfin : ∫⁻ x, ‖f x‖ₑ ^ p ≠ ⊤ := by
      have h := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hP0 ENNReal.ofReal_ne_top
        (f.memLp (ENNReal.ofReal p) volume).eLpNorm_lt_top
      rw [ENNReal.toReal_ofReal hp0.le] at h
      exact h.ne
    have hlim : Tendsto (fun n => ∫⁻ x, ‖φ n x - f x‖ₑ ^ p) atTop (𝓝 0) := by
      rw [← lintegral_zero]
      refine tendsto_lintegral_of_dominated_convergence (fun x => ‖f x‖ₑ ^ p)
        (fun n => ?_) (fun n => ae_of_all _ fun x => ?_) hfin (ae_of_all _ fun x => ?_)
      · exact ((φ n).continuous.sub f.continuous).eNorm.measurable.pow_const p
      · -- `|φ_n − f| = |η (t_n x) − 1| |f| ≤ |f|`
        refine ENNReal.rpow_le_rpow ?_ hp0.le
        rw [← ofReal_norm, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : φ n x - f x = ((χ (t n • x) - 1 : ℝ) : ℂ) * f x := by
          rw [hφ]
          push_cast
          ring
        rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_of_le_one_left (norm_nonneg _) (abs_le.2 ⟨?_, ?_⟩)
        · linarith [χ.nonneg (x := t n • x)]
        · linarith [χ.le_one (x := t n • x)]
      · -- `φ_n (x) = f (x)` as soon as `|t_n x| ≤ 1`
        have hx : ∀ᶠ n in atTop, t n • x ∈ Metric.closedBall (0 : V) 1 := by
          have := ht.smul_const x
          rw [zero_smul] at this
          exact this.eventually (Metric.closedBall_mem_nhds 0 one_pos)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hx] with n hn
        rw [hφ, χ.one_of_mem_closedBall hn, Complex.ofReal_one, one_mul, sub_self, eNorm_zero,
          ENNReal.zero_rpow_of_pos hp0]
    have := hlim.ennrpow_const (1 / p)
    rw [ENNReal.zero_rpow_of_pos (by positivity)] at this
    refine this.congr fun n => ?_
    exact (heq _ ((φ n).continuous.sub f.continuous)).symm
  · -- `𝓕 φ_n → 𝓕 f` in `L^1`: the mollifiers
    have h := (tendsto_eLpNorm_mollify_sub hψ (𝓕 f) le_rfl).comp ht
    rw [ENNReal.ofReal_one] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, hFφ n]

end HarmonicAnalysis

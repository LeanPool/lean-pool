/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Defs

/-!
# Fourier multipliers on a Euclidean space

`V` is a finite-dimensional real inner product space with its Lebesgue measure `volume`, and the
Fourier transform is Mathlib's, `𝓕 f (ξ) = ∫ e^{−2πi ⟨v, ξ⟩} f (v) dv`.

* `HarmonicAnalysis.fourierMultiplier m f = 𝓕⁻¹ (m · 𝓕 f)`, the Fourier multiplier with symbol
  `m : V → ℂ`, applied to `f : V → ℂ`.
* `HarmonicAnalysis.multiplierNorm m p`, the norm of `f ↦ 𝓕⁻¹ (m · 𝓕 f)` on `L^p (V)`, computed on
  the dense subspace of Schwartz functions: `⨆_{f ∈ 𝓢(V)} ‖T_m f‖_p / ‖f‖_p` in `ℝ≥0∞` (with
  `0 / 0 = 0`; it is `∞` when `T_m` is unbounded on `L^p`).

## Main results

* `HarmonicAnalysis.continuous_fourierMultiplier`: `T_m f` is continuous for every Schwartz
  function `f` (when `m · 𝓕 f` is not integrable, Lean's integral makes it `0`).
* `HarmonicAnalysis.eLpNorm_fourierMultiplier_le`: `‖T_m f‖_p ≤ ‖T_m‖_p ‖f‖_p`.
* `HarmonicAnalysis.enorm_fourierMultiplier_sub_le`: `|T_m f (x) − T_m g (x)| ≤ ‖𝓕 f − 𝓕 g‖₁` for
  `|m| ≤ 1`, so that `T_m f_j → T_m f` uniformly when `𝓕 f_j → 𝓕 f` in `L¹`.
* `HarmonicAnalysis.div_le_multiplierNorm_of_tendsto` (density): the norm over Schwartz functions
  bounds the ratio `‖v‖_p / ‖u‖_p` for every pair `(u, v)` that is an `L^p`-limit of pairs
  `(φ_k, T_m φ_k)` with `φ_k` Schwartz, that is, for `T_m` on the closure of its graph over
  Schwartz functions. This is how `T_m` is applied to functions of Sobolev spaces that are not
  Schwartz functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform ENNReal

namespace HarmonicAnalysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- `m · 𝓕 f` is integrable for a bounded measurable symbol `m` and a Schwartz function `f`. -/
theorem integrable_smul_fourier {m : V → ℂ} (hm : Measurable m) (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C)
    (f : 𝓢(V, ℂ)) : Integrable (fun ξ => m ξ • 𝓕 (f : V → ℂ) ξ) := by
  obtain ⟨C, hC⟩ := hmb
  have : Integrable (𝓕 (f : V → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 f).integrable
  simpa [smul_eq_mul] using this.bdd_mul hm.aestronglyMeasurable (ae_of_all _ hC)

/-- `T_m f` is continuous for every Schwartz function `f`. -/
theorem continuous_fourierMultiplier (m : V → ℂ) (f : 𝓢(V, ℂ)) :
    Continuous (fourierMultiplier m f) := by
  have hL : Continuous fun p : V × V ↦ (-innerₗ V) p.1 p.2 := by
    simp only [LinearMap.neg_apply, innerₗ_apply_apply]
    fun_prop
  by_cases hg : Integrable (fun ξ => m ξ • 𝓕 (f : V → ℂ) ξ)
  · exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar hL hg
  · have : fourierMultiplier m f = 0 := by
      ext w
      exact integral_undef (mt (VectorFourier.fourierIntegral_convergent_iff
        Real.continuous_fourierChar hL w).1 hg)
    rw [this]
    exact continuous_const

/-- `‖T_m f‖_p ≤ ‖T_m‖_p ‖f‖_p` for every Schwartz function `f`. -/
theorem eLpNorm_fourierMultiplier_le (m : V → ℂ) (p : ℝ) (f : 𝓢(V, ℂ)) :
    eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume ≤
      multiplierNorm m p * eLpNorm (f : V → ℂ) (ENNReal.ofReal p) volume := by
  have hle : eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume /
      eLpNorm (f : V → ℂ) (ENNReal.ofReal p) volume ≤ multiplierNorm m p :=
    le_iSup (fun f : 𝓢(V, ℂ) => eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume /
      eLpNorm (f : V → ℂ) (ENNReal.ofReal p) volume) f
  by_cases h0 : eLpNorm (f : V → ℂ) (ENNReal.ofReal p) volume = 0
  · rcases eq_or_ne (ENNReal.ofReal p) 0 with hp | hp
    · rw [hp, eLpNorm_exponent_zero (continuous_fourierMultiplier m f).aestronglyMeasurable]
      exact zero_le
    · have hf : (f : V → ℂ) = 0 := by
        rw [eLpNorm_eq_zero_iff hp] at h0
        exact (f.continuous.ae_eq_iff_eq volume continuous_zero).1 h0
      have hT : fourierMultiplier m f = 0 := by
        ext w
        simp [fourierMultiplier, hf, Real.fourier_eq, Real.fourierInv_eq]
      simp [hT]
  · calc eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume
        = eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume /
            eLpNorm (f : V → ℂ) (ENNReal.ofReal p) volume *
            eLpNorm (f : V → ℂ) (ENNReal.ofReal p) volume :=
          (ENNReal.div_mul_cancel h0 (f.memLp _).eLpNorm_lt_top.ne).symm
      _ ≤ _ := by gcongr

/-- `|T_m f (x) − T_m g (x)| ≤ ‖𝓕 f − 𝓕 g‖₁` for Schwartz `f`, `g` and a measurable symbol with
`|m| ≤ 1`: `T_m f − T_m g` is the inverse Fourier transform of `m (𝓕 f − 𝓕 g)`. -/
theorem enorm_fourierMultiplier_sub_le {m : V → ℂ} (hm : Measurable m) (hm1 : ∀ ξ, ‖m ξ‖ ≤ 1)
    (f g : 𝓢(V, ℂ)) (x : V) :
    ‖fourierMultiplier m f x - fourierMultiplier m g x‖ₑ ≤
      eLpNorm (fun ξ => 𝓕 (f : V → ℂ) ξ - 𝓕 (g : V → ℂ) ξ) 1 volume := by
  have hL : Continuous fun p : V × V ↦ (-innerₗ V) p.1 p.2 := by
    simp only [LinearMap.neg_apply, innerₗ_apply_apply]
    fun_prop
  set a : V → ℂ := fun ξ => m ξ • 𝓕 (f : V → ℂ) ξ
  set b : V → ℂ := fun ξ => m ξ • 𝓕 (g : V → ℂ) ξ
  have ha : Integrable a := integrable_smul_fourier hm ⟨1, hm1⟩ f
  have hb : Integrable b := integrable_smul_fourier hm ⟨1, hm1⟩ g
  have hadd := VectorFourier.fourierIntegral_add (μ := volume) (L := -innerₗ V)
    Real.continuous_fourierChar hL (ha.sub hb) hb
  rw [sub_add_cancel] at hadd
  have heq : fourierMultiplier m f x - fourierMultiplier m g x =
      VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V) (a - b) x := by
    have e := congrFun hadd x
    simp only [Pi.add_apply] at e
    change VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V) a x -
      VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V) b x = _
    rw [e, add_sub_cancel_right]
  rw [heq]
  calc ‖VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V) (a - b) x‖ₑ
      ≤ ENNReal.ofReal (∫ ξ, ‖(a - b) ξ‖) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal
          (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _)
    _ = ∫⁻ ξ, ‖(a - b) ξ‖ₑ := ofReal_integral_norm_eq_lintegral_eNorm (ha.sub hb)
    _ ≤ ∫⁻ ξ, ‖𝓕 (f : V → ℂ) ξ - 𝓕 (g : V → ℂ) ξ‖ₑ := lintegral_mono fun ξ => by
        simp only [Pi.sub_apply, a, b, ← smul_sub, eNorm_smul]
        calc ‖m ξ‖ₑ * ‖𝓕 (f : V → ℂ) ξ - 𝓕 (g : V → ℂ) ξ‖ₑ
            ≤ 1 * ‖𝓕 (f : V → ℂ) ξ - 𝓕 (g : V → ℂ) ξ‖ₑ := by
              gcongr
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_one.2 (hm1 ξ)
          _ = _ := one_mul _
    _ = _ := (eLpNorm_one_eq_lintegral_eNorm
        (((𝓕 f).continuous.sub (𝓕 g).continuous).aestronglyMeasurable)).symm

/-- Density: if Schwartz functions `φ_k` satisfy `φ_k → u` and `T_m φ_k → v` in `L^p`, `1 ≤ p`,
then `‖v‖_p / ‖u‖_p ≤ ‖T_m‖_p`. -/
theorem div_le_multiplierNorm_of_tendsto (m : V → ℂ) {p : ℝ} (hp : 1 ≤ p) {φ : ℕ → 𝓢(V, ℂ)}
    {u v : V → ℂ}
    (hφu : Tendsto (fun k => eLpNorm (fun x => φ k x - u x) (ENNReal.ofReal p) volume) atTop
      (𝓝 0))
    (hφv : Tendsto (fun k => eLpNorm (fun x => fourierMultiplier m (φ k) x - v x)
      (ENNReal.ofReal p) volume) atTop (𝓝 0)) :
    eLpNorm v (ENNReal.ofReal p) volume / eLpNorm u (ENNReal.ofReal p) volume ≤
      multiplierNorm m p := by
  set P := ENNReal.ofReal p
  set M := multiplierNorm m p
  rcases eq_or_ne M ⊤ with hM | hM
  · rw [hM]
    exact le_top
  refine ENNReal.div_le_of_le_mul ?_
  have hP : 1 ≤ P := by simpa [P] using ENNReal.ofReal_le_ofReal hp
  have hlim : Tendsto (fun k => eLpNorm (fun x => fourierMultiplier m (φ k) x - v x) P volume +
      M * (eLpNorm (fun x => φ k x - u x) P volume + eLpNorm u P volume)) atTop
      (𝓝 (M * eLpNorm u P volume)) := by
    have := hφv.add (ENNReal.Tendsto.const_mul (hφu.add_const (eLpNorm u P volume)) (Or.inr hM))
    simpa using this
  refine ge_of_tendsto' hlim fun k => ?_
  have h1 : eLpNorm v P volume ≤ eLpNorm (fun x => fourierMultiplier m (φ k) x - v x) P volume +
      eLpNorm (fourierMultiplier m (φ k)) P volume := by
    have := eLpNorm_sub_le (μ := volume) (f := fourierMultiplier m (φ k))
      (g := fun x => fourierMultiplier m (φ k) x - v x) hP
    rw [add_comm]
    convert this using 2
    ext x
    simp
  have h2 : eLpNorm (φ k : V → ℂ) P volume ≤
      eLpNorm (fun x => φ k x - u x) P volume + eLpNorm u P volume := by
    have := eLpNorm_add_le (μ := volume) (f := fun x => φ k x - u x) (g := u) hP
    convert this using 2
    ext x
    simp
  calc eLpNorm v P volume
      ≤ eLpNorm (fun x => fourierMultiplier m (φ k) x - v x) P volume +
          eLpNorm (fourierMultiplier m (φ k)) P volume := h1
    _ ≤ eLpNorm (fun x => fourierMultiplier m (φ k) x - v x) P volume +
          M * eLpNorm (φ k : V → ℂ) P volume := by
        gcongr
        exact eLpNorm_fourierMultiplier_le m p (φ k)
    _ ≤ _ := by gcongr

end HarmonicAnalysis

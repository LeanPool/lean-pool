/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Basic
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Extension
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Sobolev.Mollify
public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Basic
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.CompactSupport
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# The Beurling–Ahlfors transform on `L² (ℂ)`

`HarmonicAnalysis.beurlingL2` is the Beurling–Ahlfors transform `𝓑` as a bounded operator on
`L² (ℂ)`, the extension of `𝓑` from the Schwartz functions:

* `HarmonicAnalysis.beurlingL2_toLp`: `𝓑 f = beurlingPow 1 f` for Schwartz `f`;
* `HarmonicAnalysis.norm_beurlingL2_le`: `‖𝓑‖_{L² → L²} ≤ 1`, from Tau Ceti's operator bound;
* `HarmonicAnalysis.eLpNorm_beurlingL2_two_le`: `‖𝓑 u‖₂ ≤ ‖u‖₂`, with `eLpNorm`;
* `HarmonicAnalysis.eLpNorm_beurlingL2_le`: on `L² ∩ L^p`, `‖𝓑 u‖_p ≤ ‖𝓑‖_p ‖u‖_p`, `1 ≤ p < ∞`,
  where `‖𝓑‖_p = beurlingPowNorm 1 p` is the norm on Schwartz functions: the operator on `L²`
  and the extension of `𝓑` to `L^p` agree on `L² ∩ L^p`;
* `HarmonicAnalysis.eLpNorm_beurlingL2_toLp_le`: the same for a function `w ∈ L² ∩ L^p`;
* `HarmonicAnalysis.beurlingL2_dzbar`: `𝓑 (∂_zbar g) = ∂g` for every compactly supported `g ∈ L²`
with
  a weak derivative in `L²`, the characterization `𝓑 ∘ ∂_zbar = ∂` of the Beurling–Ahlfors transform
  beyond the Schwartz functions.

## Proofs

`beurlingPowNorm_one_two_le`: by `HarmonicAnalysis.beurlingPowNorm_one_le_iff`, it suffices that
`‖∂u‖₂ ≤ ‖∂_zbar u‖₂` for smooth compactly supported `u`; by Plancherel for Schwartz functions,
`‖∂u‖₂ = ‖π i (conj ξ) 𝓕u‖₂ = ‖π i ξ 𝓕u‖₂ = ‖∂_zbar u‖₂`.

`beurlingL2` is Tau Ceti's spectral multiplier. Its agreement with the integral formula on
Schwartz inputs follows by identifying the inverse Fourier transforms in tempered distributions.

`eLpNorm_beurlingL2_le`: `u ∈ L² ∩ L^p` is the limit, in `L²` and in `L^p` at once, of smooth
compactly supported functions, the mollifications `ρ_k ⋆ (1_{B_R} u)` of truncations
(`HarmonicAnalysis.tendsto_eLpNorm_convolution_sub`); `𝓑` of these converges to `𝓑 u` in `L²`,
hence almost everywhere along a subsequence, and Fatou's lemma bounds `‖𝓑 u‖_p` by
`liminf ‖𝓑‖_p ‖ρ_k ⋆ (1_{B_R} u)‖_p = ‖𝓑‖_p ‖u‖_p`.

`beurlingL2_dzbar`: the mollifications `g_n = ρ_n ⋆ g` are smooth with compact support, hence
Schwartz functions, with `𝓑 (∂_zbar g_n) = ∂g_n` (`HarmonicAnalysis.beurlingPow_dzbarCLM_pow`); and
`∂_zbar g_n = ρ_n ⋆ ∂_zbar g → ∂_zbar g`, `∂g_n = ρ_n ⋆ ∂g → ∂g` in `L²`
(`HarmonicAnalysis.hasFDerivAt_convolution_of_hasWeakFDerivOn`,
`HarmonicAnalysis.tendsto_eLpNorm_convolution_sub`). `𝓑` is continuous on `L²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped ENNReal SchwartzMap FourierTransform ComplexConjugate Convolution

namespace HarmonicAnalysis

/-! ### The norm of `𝓑` on `L²` -/

/-- Plancherel for Schwartz functions: `‖𝓕 f‖₂ = ‖f‖₂`. -/
private lemma bl2_eLpNorm_fourier (f : 𝓢(ℂ, ℂ)) :
    eLpNorm (𝓕 (f : ℂ → ℂ)) 2 volume = eLpNorm (f : ℂ → ℂ) 2 volume := by
  have h : ‖(𝓕 f).toLp 2 volume‖ = ‖f.toLp 2 volume‖ := SchwartzMap.norm_fourier_toL2_eq f
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp] at h
  have h' := (ENNReal.toReal_eq_toReal_iff' ((𝓕 f).memLp 2 volume).eLpNorm_ne_top
    (f.memLp 2 volume).eLpNorm_ne_top).1 h
  rwa [SchwartzMap.fourier_coe] at h'

/-- `‖∂U‖₂ = ‖∂_zbar U‖₂` for Schwartz `U`: on the Fourier side, `|π i (conj ξ)| = |π i ξ|`. -/
private lemma bl2_eLpNorm_dzCLM (U : 𝓢(ℂ, ℂ)) :
    eLpNorm (dzCLM U : ℂ → ℂ) 2 volume = eLpNorm (dzbarCLM U : ℂ → ℂ) 2 volume := by
  rw [← bl2_eLpNorm_fourier, ← bl2_eLpNorm_fourier]
  refine eLpNorm_congr_norm_ae (𝓕 (dzCLM U)).continuous.aestronglyMeasurable
    (𝓕 (dzbarCLM U)).continuous.aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
  rw [fourier_dzCLM, fourier_dzbarCLM]
  simp only [norm_smul, norm_mul, Complex.norm_conj]

/-- `‖𝓑 f‖₂ ≤ ‖f‖₂` for Schwartz `f`: `‖𝓑‖₂ ≤ 1`. -/
theorem beurlingPowNorm_one_two_le : beurlingPowNorm 1 2 ≤ 1 := by
  refine (beurlingPowNorm_one_le_iff one_lt_two).2 fun u hu huc => ?_
  set U : 𝓢(ℂ, ℂ) := huc.toSchwartzMap hu
  have hU : (U : ℂ → ℂ) = u := rfl
  have h1 : dz u = dzCLM U := by
    rw [← hU]
    exact funext fun z => (dzCLM_apply U z).symm
  have h2 : dzbar u = dzbarCLM U := by
    rw [← hU]
    exact funext fun z => (dzbarCLM_apply U z).symm
  rw [one_mul, h1, h2, ENNReal.ofReal_ofNat, bl2_eLpNorm_dzCLM]

/-! ### The operator on `L²` -/

/-- `𝓑 f ∈ L²` for Schwartz `f`. -/
theorem memLp_beurlingPow_one_two (f : 𝓢(ℂ, ℂ)) : MemLp (beurlingPow 1 f) 2 volume := by
  have h := memLp_fourierMultiplier (m := fun ξ => beurlingSymbol ξ ^ 1) (p := 2)
    (beurlingPowNorm_one_two_le.trans_lt ENNReal.one_lt_top).ne f
  rwa [ENNReal.ofReal_ofNat] at h

/-- Tau Ceti's Beurling–Ahlfors transform on complex-valued `L²` functions. -/
abbrev beurlingL2 : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  TauCeti.beurlingL2 ℂ

/-- `𝓑` on the Schwartz functions, as a linear map into `L² (ℂ)`. -/
def beurlingSchwartzToL2 : 𝓢(ℂ, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  beurlingL2.toLinearMap.comp (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℂ)).toLinearMap

/-- `𝓑 f = beurlingPow 1 f` for Schwartz `f`. -/
theorem beurlingL2_toLp (f : 𝓢(ℂ, ℂ)) :
    beurlingL2 (f.toLp 2) =ᵐ[volume] beurlingPow 1 f := by
  let product : Lp ℂ 2 (volume : Measure ℂ) := TauCeti.beurlingSymbolLinf • 𝓕 (f.toLp 2)
  have hproduct : product =ᵐ[volume] fun ξ => beurlingSymbol ξ • 𝓕 (f : ℂ → ℂ) ξ := by
    dsimp only [product]
    rw [SchwartzMap.toLp_fourier_eq]
    filter_upwards [Lp.coeFn_lpSMul (r := 2) TauCeti.beurlingSymbolLinf ((𝓕 f).toLp 2),
      TauCeti.coeFn_beurlingSymbolLinf, (𝓕 f).coeFn_toLp 2] with ξ hmul hsymbol hfourier
    rw [hmul, Pi.smul_apply', hsymbol, hfourier, SchwartzMap.fourier_coe]
    by_cases hξ : ξ = 0
    · simp [hξ, TauCeti.beurlingSymbol_zero, beurlingSymbol]
    rw [(eq_div_iff hξ).2 (TauCeti.beurlingSymbol_mul ξ), beurlingSymbol]
  have hintegrable : Integrable (fun ξ => beurlingSymbol ξ • 𝓕 (f : ℂ → ℂ) ξ) :=
    integrable_smul_fourier measurable_beurlingSymbol ⟨1, norm_beurlingSymbol_le⟩ f
  change ⇑(TauCeti.beurlingL2 ℂ (f.toLp 2)) =ᵐ[volume] beurlingPow 1 f
  rw [TauCeti.beurlingL2_def, Lp.fourierMultiplierCLM_apply]
  simpa only [beurlingPow, fourierMultiplier, pow_one] using
    (Lp.ae_eq_of_toTemperedDistribution_apply_eq (𝓕⁻ product)
      (continuous_fourierMultiplier beurlingSymbol f).locallyIntegrable fun φ => by
        rw [← Lp.fourierInv_toTemperedDistribution_eq]
        exact Lp.fourierInv_toTemperedDistribution_apply _ hintegrable hproduct φ)

/-- `‖𝓑‖_{L² → L²} ≤ 1`. -/
theorem norm_beurlingL2_le : ‖beurlingL2‖ ≤ 1 :=
  TauCeti.norm_beurlingL2_le

/-! ### Mollifiers and truncations -/

/-- The bump of radii `1 / (n + 2) < 1 / (n + 1)`. -/
private def bl2_bump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / ((n : ℝ) + 2)
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith

/-- The radii of the bumps tend to `0`. -/
private lemma bl2_tendsto_rOut : Tendsto (fun n => (bl2_bump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Truncation: `‖1_{|z| > n} f‖_q → 0` for `f ∈ L^q`, `0 < q < ∞` (dominated convergence). -/
private lemma bl2_tendsto_eLpNorm_indicator_compl {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞)
    {f : ℂ → ℂ} (hf : MemLp f q volume) :
    Tendsto (fun n : ℕ => eLpNorm ((Metric.closedBall (0 : ℂ) n)ᶜ.indicator f) q volume) atTop
      (𝓝 0) := by
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable ((Metric.closedBall (0 : ℂ) n)ᶜ.indicator f) volume := fun n =>
    hf.aestronglyMeasurable.indicator measurableSet_closedBall.compl
  have hint : Tendsto (fun n : ℕ =>
      ∫⁻ z, ‖(Metric.closedBall (0 : ℂ) n)ᶜ.indicator f z‖ₑ ^ q.toReal) atTop
      (𝓝 (∫⁻ _ : ℂ, 0)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun z => ‖f z‖ₑ ^ q.toReal)
      (fun n => (hmeas n).eNorm.pow_const _) (fun n => ae_of_all _ fun z => ?_) ?_
      (ae_of_all _ fun z => ?_)
    · exact ENNReal.rpow_le_rpow (eNorm_indicator_le_eNorm_self _ _) hq'.le
    · exact (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hq0 hq hf.eLpNorm_lt_top).ne
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
      have hz : z ∈ Metric.closedBall (0 : ℂ) n := by
        rw [mem_closedBall_zero_iff]
        exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
      rw [Set.indicator_of_notMem (show z ∉ (Metric.closedBall (0 : ℂ) n)ᶜ from fun h' => h' hz),
        eNorm_zero, ENNReal.zero_rpow_of_pos hq']
  rw [lintegral_zero] at hint
  have h1 := hint.ennrpow_const (1 / q.toReal)
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at h1
  refine h1.congr fun n => ?_
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq (hmeas n)]

/-- `u ∈ L² ∩ L^q`, `1 ≤ q < ∞`, is within `ε` of a Schwartz function, in `L²` and in `L^q` at
once: a mollification `ρ_k ⋆ (1_{B_R} u)` of a truncation. -/
private lemma bl2_exists_schwartz_le {u : ℂ → ℂ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hq' : q ≠ ∞)
    (hu2 : MemLp u 2 volume) (huq : MemLp u q volume) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ ψ : 𝓢(ℂ, ℂ), eLpNorm (⇑ψ - u) 2 volume ≤ ε ∧ eLpNorm (⇑ψ - u) q volume ≤ ε := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- the truncation `v = 1_{B_R} u`
  obtain ⟨R, hR2, hRq⟩ := ((bl2_tendsto_eLpNorm_indicator_compl two_ne_zero ENNReal.ofNat_ne_top
    hu2).eventually (ge_mem_nhds hε2) |>.and ((bl2_tendsto_eLpNorm_indicator_compl
    (zero_lt_one.trans_le hq).ne' hq' huq).eventually (ge_mem_nhds hε2))).exists
  set v := (Metric.closedBall (0 : ℂ) R).indicator u
  have hv2 : MemLp v 2 volume := MemLp.indicator measurableSet_closedBall.nullMeasurableSet hu2
  have hvq : MemLp v q volume := MemLp.indicator measurableSet_closedBall.nullMeasurableSet huq
  have hvc : HasCompactSupport v :=
    HasCompactSupport.intro (isCompact_closedBall 0 R) fun z hz => Set.indicator_of_notMem hz u
  have hvl : LocallyIntegrable v volume := hv2.locallyIntegrable one_le_two
  have hvu : ∀ r, eLpNorm (v - u) r volume =
      eLpNorm ((Metric.closedBall (0 : ℂ) R)ᶜ.indicator u) r volume := fun r => by
    rw [eLpNorm_sub_comm, Set.indicator_compl]
  -- the mollification `ρ_k ⋆ v`
  obtain ⟨k, hk2, hkq⟩ := ((tendsto_eLpNorm_convolution_sub bl2_tendsto_rOut one_le_two
    ENNReal.ofNat_ne_top hv2).eventually (ge_mem_nhds hε2) |>.and
    ((tendsto_eLpNorm_convolution_sub bl2_tendsto_rOut hq hq' hvq).eventually
      (ge_mem_nhds hε2))).exists
  set ρ := (bl2_bump k).normed volume
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ ⋆[lsmul ℝ ℝ] v) :=
    (bl2_bump k).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (bl2_bump k).contDiff_normed hvl
  have hcs : HasCompactSupport (ρ ⋆[lsmul ℝ ℝ] v) :=
    (bl2_bump k).hasCompactSupport_normed.convolution _ hvc
  have e : ⇑(hcs.toSchwartzMap hsm) - u = (ρ ⋆[lsmul ℝ ℝ] v - v) + (v - u) := by
    rw [sub_add_sub_cancel]
    rfl
  -- `‖ψ − u‖_r ≤ ‖ρ_k ⋆ v − v‖_r + ‖v − u‖_r ≤ ε / 2 + ε / 2`
  have hsplit : ∀ r, 1 ≤ r → eLpNorm (ρ ⋆[lsmul ℝ ℝ] v - v) r volume ≤ ε / 2 →
      eLpNorm ((Metric.closedBall (0 : ℂ) R)ᶜ.indicator u) r volume ≤ ε / 2 →
      eLpNorm (⇑(hcs.toSchwartzMap hsm) - u) r volume ≤ ε := fun r hr h₁ h₂ => by
    rw [e, ← ENNReal.add_halves ε]
    exact (eLpNorm_add_le hr).trans (add_le_add h₁ ((hvu r).trans_le h₂))
  exact ⟨_, hsplit 2 one_le_two hk2 hR2, hsplit q hq hkq hRq⟩

/-- `u ∈ L² ∩ L^q`, `1 ≤ q < ∞`, is the limit in `L²` and in `L^q` at once of Schwartz functions
(indeed smooth compactly supported ones). -/
private lemma bl2_exists_tendsto {u : ℂ → ℂ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hq' : q ≠ ∞)
    (hu2 : MemLp u 2 volume) (huq : MemLp u q volume) :
    ∃ φ : ℕ → 𝓢(ℂ, ℂ), Tendsto (fun n => eLpNorm (⇑(φ n) - u) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (⇑(φ n) - u) q volume) atTop (𝓝 0) := by
  choose φ hφ2 hφq using fun n : ℕ =>
    bl2_exists_schwartz_le hq hq' hu2 huq (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))
  exact ⟨φ, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ => zero_le) hφ2,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ => zero_le) hφq⟩

/-! ### `𝓑` on `L² ∩ L^p` -/

/-- **`𝓑` on `L² ∩ L^p`**: `‖𝓑 u‖_p ≤ ‖𝓑‖_p ‖u‖_p` for `u ∈ L² ∩ L^p`, `1 ≤ p < ∞`. -/
theorem eLpNorm_beurlingL2_le {p : ℝ} (hp : 1 ≤ p) (u : Lp ℂ 2 (volume : Measure ℂ))
    (hu : MemLp u (ENNReal.ofReal p) volume) :
    eLpNorm (beurlingL2 u) (ENNReal.ofReal p) volume ≤
      beurlingPowNorm 1 p * eLpNorm u (ENNReal.ofReal p) volume := by
  set P := ENNReal.ofReal p
  have hP : 1 ≤ P := by simpa [P] using ENNReal.ofReal_le_ofReal hp
  have hP0 : P ≠ 0 := (zero_lt_one.trans_le hP).ne'
  set M := beurlingPowNorm 1 p
  rcases eq_or_ne M ⊤ with hM | hM
  · by_cases h0 : eLpNorm u P volume = 0
    · -- `u = 0`, hence `𝓑 u = 0`
      have hu0 : u = 0 := Lp.eq_zero_iff_ae_eq_zero.2 ((eLpNorm_eq_zero_iff hP0).1 h0)
      rw [hu0, map_zero, eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
      exact zero_le
    · rw [hM, ENNReal.top_mul h0]
      exact le_top
  obtain ⟨φ, hφ2, hφP⟩ := bl2_exists_tendsto hP ENNReal.ofReal_ne_top (Lp.memLp u) hu
  -- `φ_n → u` in `L²`, hence `𝓑 φ_n → 𝓑 u` in `L²`
  have hL2 : Tendsto (fun n => (φ n).toLp 2 volume) atTop (𝓝 u) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hφ2.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(φ n).coeFn_toLp 2 volume] with x hx
    simp [hx]
  have hB : Tendsto (fun n => beurlingL2 ((φ n).toLp 2 volume)) atTop (𝓝 (beurlingL2 u)) :=
    (beurlingL2.continuous.tendsto u).comp hL2
  -- a subsequence converges almost everywhere
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hB).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂volume, ∀ n, beurlingL2 ((φ n).toLp 2 volume) x = beurlingPow 1 (φ n) x :=
    ae_all_iff.2 fun n => beurlingL2_toLp (φ n)
  have hlim : ∀ᵐ x ∂volume,
      Tendsto (fun n => beurlingPow 1 (φ (ns n)) x) atTop (𝓝 (beurlingL2 u x)) := by
    filter_upwards [hae, hall] with x hx hx'
    simpa only [hx'] using hx
  -- Fatou's lemma
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := P) (μ := volume)
    (fun n => (continuous_fourierMultiplier _ (φ (ns n))).aestronglyMeasurable) _
    (Lp.aestronglyMeasurable _) hlim
  have hbound : ∀ n, eLpNorm (beurlingPow 1 (φ (ns n))) P volume ≤
      M * (eLpNorm (⇑(φ (ns n)) - ⇑u) P volume + eLpNorm u P volume) := fun n => by
    have e := eLpNorm_add_le (μ := volume) (f := ⇑(φ (ns n)) - ⇑u) (g := ⇑u) hP
    rw [sub_add_cancel] at e
    calc eLpNorm (beurlingPow 1 (φ (ns n))) P volume ≤ M * eLpNorm (φ (ns n)) P volume :=
          eLpNorm_fourierMultiplier_le _ p (φ (ns n))
      _ ≤ _ := by gcongr
  have hlim2 : Tendsto (fun n => M * (eLpNorm (⇑(φ (ns n)) - ⇑u) P volume + eLpNorm u P volume))
      atTop (𝓝 (M * eLpNorm u P volume)) := by
    simpa using ENNReal.Tendsto.const_mul ((hφP.comp hns.tendsto_atTop).add_const _) (Or.inr hM)
  calc eLpNorm (beurlingL2 u) P volume
      ≤ atTop.liminf fun n => eLpNorm (beurlingPow 1 (φ (ns n))) P volume := hfatou
    _ ≤ atTop.liminf fun n => M * (eLpNorm (⇑(φ (ns n)) - ⇑u) P volume +
          eLpNorm u P volume) := liminf_le_liminf (Eventually.of_forall hbound)
    _ = M * eLpNorm u P volume := hlim2.liminf_eq

/-- `‖𝓑 u‖₂ ≤ ‖u‖₂` for `u ∈ L²`. -/
theorem eLpNorm_beurlingL2_two_le (u : Lp ℂ 2 (volume : Measure ℂ)) :
    eLpNorm (beurlingL2 u) 2 volume ≤ eLpNorm u 2 volume := by
  have h := eLpNorm_beurlingL2_le one_le_two u (by rw [ENNReal.ofReal_ofNat]; exact Lp.memLp u)
  rw [ENNReal.ofReal_ofNat] at h
  calc eLpNorm (beurlingL2 u) 2 volume ≤ beurlingPowNorm 1 2 * eLpNorm u 2 volume := h
    _ ≤ 1 * eLpNorm u 2 volume := by gcongr; exact beurlingPowNorm_one_two_le
    _ = eLpNorm u 2 volume := one_mul _

/-- `eLpNorm_beurlingL2_le` for a function `w ∈ L² ∩ L^p`, `1 ≤ p < ∞`:
`‖𝓑 w‖_p ≤ ‖𝓑‖_p ‖w‖_p`. -/
theorem eLpNorm_beurlingL2_toLp_le {p : ℝ} (hp : 1 ≤ p) {w : ℂ → ℂ} (hw : MemLp w 2 volume)
    (hwp : MemLp w (ENNReal.ofReal p) volume) :
    eLpNorm (beurlingL2 (hw.toLp w)) (ENNReal.ofReal p) volume ≤
      beurlingPowNorm 1 p * eLpNorm w (ENNReal.ofReal p) volume := by
  have h := eLpNorm_beurlingL2_le hp (hw.toLp w) (hwp.ae_eq hw.coeFn_toLp.symm)
  rwa [eLpNorm_congr_ae hw.coeFn_toLp] at h

/-! ### `𝓑 (∂_zbar g) = ∂g` -/

/-- A continuous linear map commutes with mollification: `L ((ρ ⋆ f) z) = (ρ ⋆ (L ∘ f)) z`. -/
private lemma bl2_map_convolution {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [CompleteSpace E'] [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
    (L : E' →L[ℝ] F') (φ : ContDiffBump (0 : ℂ)) {f : ℂ → E'} (hf : LocallyIntegrable f volume)
    (z : ℂ) :
    L ((φ.normed volume ⋆[lsmul ℝ ℝ] f) z) =
      (φ.normed volume ⋆[lsmul ℝ ℝ] (fun w => L (f w))) z := by
  have hex : ConvolutionExistsAt (φ.normed volume) f z (lsmul ℝ ℝ) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left _ φ.continuous_normed hf z
  rw [convolution_def, convolution_def, ← L.integral_comp_comm hex]
  simp only [lsmul_apply, map_smul]

/-- `∂_zbar`, as a continuous real-linear functional on the real-linear maps of `ℂ`. -/
private def bl2_dzbarL : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2⁻¹ : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) +
    Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I)

/-- `∂`, as a continuous real-linear functional on the real-linear maps of `ℂ`. -/
private def bl2_dzL : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2⁻¹ : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) -
    Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I)

/-- `bl2_dzbarL A = ∂_zbar A`. -/
private lemma bl2_dzbarL_apply (A : ℂ →L[ℝ] ℂ) : bl2_dzbarL A = dzbarPart A := by
  simp [bl2_dzbarL, dzbarPart, smul_eq_mul, mul_add]

/-- `bl2_dzL A = ∂A`. -/
private lemma bl2_dzL_apply (A : ℂ →L[ℝ] ℂ) : bl2_dzL A = dzPart A := by
  simp [bl2_dzL, dzPart, smul_eq_mul, mul_sub]

/-- **`𝓑 (∂_zbar g) = ∂g`** for a compactly supported `g ∈ L² (ℂ)` with a weak derivative `Dg ∈ L²
(ℂ)`
on the whole plane. -/
theorem beurlingL2_dzbar {g : ℂ → ℂ} {Dg : ℂ → ℂ →L[ℝ] ℂ} (hgc : HasCompactSupport g)
    (hg : MemLp g 2 volume) (hDg : MemLp Dg 2 volume) (h : HasWeakFDerivOn Set.univ g Dg) :
    beurlingL2 ((memLp_dzbarPart hDg).toLp _) =ᵐ[volume] fun z => dzPart (Dg z) := by
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable one_le_two
  have hDgl : LocallyIntegrable Dg volume := hDg.locallyIntegrable one_le_two
  set ρ : ℕ → ℂ → ℝ := fun n => (bl2_bump n).normed volume
  -- `g_n = ρ_n ⋆ g`, a Schwartz function
  have hsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n ⋆[lsmul ℝ ℝ] g) := fun n =>
    (bl2_bump n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (bl2_bump n).contDiff_normed hgl
  have hcs : ∀ n, HasCompactSupport (ρ n ⋆[lsmul ℝ ℝ] g) := fun n =>
    (bl2_bump n).hasCompactSupport_normed.convolution _ hgc
  set G : ℕ → 𝓢(ℂ, ℂ) := fun n => (hcs n).toSchwartzMap (hsm n)
  have hG : ∀ n, (G n : ℂ → ℂ) = ρ n ⋆[lsmul ℝ ℝ] g := fun n => rfl
  -- `D g_n = ρ_n ⋆ Dg`
  have hD : ∀ n z, fderiv ℝ (G n) z = (ρ n ⋆[lsmul ℝ ℝ] Dg) z := fun n z => by
    rw [hG]
    exact (hasFDerivAt_convolution_of_hasWeakFDerivOn (bl2_bump n) hgl hDgl h z).fderiv
  have hdzbar : ∀ n, (dzbarCLM (G n) : ℂ → ℂ) =
      ρ n ⋆[lsmul ℝ ℝ] (fun w => dzbarPart (Dg w)) := fun n => funext fun z => by
    rw [dzbarCLM_apply, ← dzbarPart_fderiv, hD, ← bl2_dzbarL_apply,
      bl2_map_convolution _ _ hDgl]
    simp only [bl2_dzbarL_apply]
    rfl
  have hdz : ∀ n, (dzCLM (G n) : ℂ → ℂ) =
      ρ n ⋆[lsmul ℝ ℝ] (fun w => dzPart (Dg w)) := fun n => funext fun z => by
    rw [dzCLM_apply, ← dzPart_fderiv, hD, ← bl2_dzL_apply, bl2_map_convolution _ _ hDgl]
    simp only [bl2_dzL_apply]
    rfl
  -- `∂_zbar g_n → ∂_zbar g` in `L²`
  have h1 : Tendsto (fun n => (dzbarCLM (G n)).toLp 2 volume) atTop
      (𝓝 ((memLp_dzbarPart hDg).toLp _)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm]
    refine (tendsto_eLpNorm_convolution_sub bl2_tendsto_rOut one_le_two ENNReal.ofNat_ne_top
      (memLp_dzbarPart hDg)).congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(dzbarCLM (G n)).coeFn_toLp 2 volume] with x hx
    rw [Pi.sub_apply, Pi.sub_apply, hx, hdzbar]
  -- `𝓑 (∂_zbar g_n) = ∂g_n → ∂g` in `L²`
  have h2 : Tendsto (fun n => beurlingL2 ((dzbarCLM (G n)).toLp 2 volume)) atTop
      (𝓝 ((memLp_dzPart hDg).toLp _)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm]
    refine (tendsto_eLpNorm_convolution_sub bl2_tendsto_rOut one_le_two ENNReal.ofNat_ne_top
      (memLp_dzPart hDg)).congr fun n => eLpNorm_congr_ae ?_
    have hB := beurlingPow_dzbarCLM_pow 1 (G n)
    simp only [pow_one] at hB
    filter_upwards [beurlingL2_toLp (dzbarCLM (G n))] with x hx
    rw [Pi.sub_apply, Pi.sub_apply, hx, hB, hdz]
  have h3 := (beurlingL2.continuous.tendsto _).comp h1
  rw [tendsto_nhds_unique h3 h2]
  exact (memLp_dzPart hDg).coeFn_toLp

end HarmonicAnalysis

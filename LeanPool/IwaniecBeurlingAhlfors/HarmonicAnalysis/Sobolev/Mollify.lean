/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Sobolev.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.FourierMultiplier.Density
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Mollification

For a bump function `φ : ContDiffBump 0` on a finite-dimensional real normed space `E` with an
additive Haar measure, `ρ = φ.normed volume` is smooth, nonnegative, of integral `1` and supported
in the ball of radius `φ.rOut`; the mollification of `f` is the convolution `ρ ⋆ f`. Mathlib
proves that `ρ ⋆ f` is smooth for locally integrable `f`
(`HasCompactSupport.contDiff_convolution_left`) and compactly supported if `f` is
(`HasCompactSupport.convolution`). Here:

* `HarmonicAnalysis.eLpNorm_convolution_le`: `‖ρ ⋆ f‖_p ≤ ‖f‖_p`, `1 ≤ p` (Young's inequality
  with `‖ρ‖₁ = 1`).
* `HarmonicAnalysis.tendsto_eLpNorm_convolution_sub`: `ρ_i ⋆ f → f` in `L^p`, `1 ≤ p < ∞`, when the
  radii `rOut` of the bumps tend to `0`.
* `HarmonicAnalysis.hasFDerivAt_convolution_of_hasWeakFDerivOn`: for `f` with a weak derivative
  `Df` on the whole space, `D (ρ ⋆ f) = ρ ⋆ Df` (mollification commutes with weak derivatives).

## Proofs

* Young's inequality: for `p < ∞` it is Minkowski's integral inequality
  `HarmonicAnalysis.eLpNorm_integral_smul_le`, applied to the translates of a strongly measurable
  version of `f`; for `p = ∞`, `|ρ ⋆ f| ≤ ‖ρ‖₁ ‖f‖_∞` everywhere (`eNorm_convolution_le`).
* The convergence: `f` is approximated in `L^p` by a continuous `g` with compact support
  (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`); `ρ_i ⋆ g → g` uniformly, with supports in the
  `1`-neighbourhood of `tsupport g` once `rOut ≤ 1`, hence in `L^p`; and
  `‖ρ_i ⋆ (f − g)‖_p ≤ ‖f − g‖_p` by Young's inequality.
* The derivative: Mathlib's `HasCompactSupport.hasFDerivAt_convolution_left` gives
  `D (ρ ⋆ f) (x) = ((Dρ) ⋆ f) (x)`, and the weak derivative tested against `y ↦ ρ (x − y)` turns
  `((Dρ) ⋆ f) (x) v` into `(ρ ⋆ Df) (x) v`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped ENNReal Convolution

namespace HarmonicAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- **Young's inequality** for a mollifier: `‖ρ ⋆ f‖_p ≤ ‖f‖_p`, `1 ≤ p ≤ ∞`, since `ρ ≥ 0` and
`∫ ρ = 1`. -/
theorem eLpNorm_convolution_le (φ : ContDiffBump (0 : E)) {p : ℝ≥0∞} (hp : 1 ≤ p) {f : E → F}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (φ.normed volume ⋆[lsmul ℝ ℝ] f) p volume ≤ eLpNorm f p volume := by
  set ρ := φ.normed volume
  have hρm : AEStronglyMeasurable ρ volume := φ.continuous_normed.aestronglyMeasurable
  have hρ1 : ∫⁻ t, ‖ρ t‖ₑ = 1 := by
    rw [lintegral_eNorm_of_nonneg (fun t => φ.nonneg_normed t),
      ← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
        (ae_of_all _ fun t => φ.nonneg_normed t), φ.integral_normed, ENNReal.ofReal_one]
  rcases eq_or_ne p ∞ with rfl | hp'
  · -- `p = ∞`: `|ρ ⋆ f| ≤ ‖ρ‖₁ ‖f‖_∞` everywhere
    have hL : ‖(lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)‖ₑ ≤ 1 := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_one.2 opNorm_lsmul_le
    have hbound : ∀ x, ‖(ρ ⋆[lsmul ℝ ℝ] f) x‖ₑ ≤ eLpNorm f ∞ volume := fun x =>
      calc ‖(ρ ⋆[lsmul ℝ ℝ] f) x‖ₑ
          ≤ ‖(lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)‖ₑ * eLpNorm ρ 1 volume * eLpNorm f ∞ volume :=
            eNorm_convolution_le _ hρm hf x
        _ ≤ 1 * 1 * eLpNorm f ∞ volume := by
            rw [eLpNorm_one_eq_lintegral_eNorm hρm, hρ1]
            gcongr
        _ = eLpNorm f ∞ volume := by rw [one_mul, one_mul]
    rw [eLpNorm_exponent_top (hρm.convolution (L := lsmul ℝ ℝ) hf)]
    exact eLpNormEssSup_le_of_ae_eNorm_bound (ae_of_all _ hbound)
  · -- `1 ≤ p < ∞`: Minkowski's integral inequality, for a strongly measurable version of `f`
    obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 1 ≤ r ∧ p = ENNReal.ofReal r :=
      ⟨p.toReal, by simpa using ENNReal.toReal_mono hp' hp, (ENNReal.ofReal_toReal hp').symm⟩
    set g := hf.mk f
    have hconv : ρ ⋆[lsmul ℝ ℝ] f = fun x => ∫ s, ρ s • g (x - s) := by
      rw [convolution_congr (lsmul ℝ ℝ) (EventuallyEq.refl _ ρ) hf.ae_eq_mk]
      ext x
      simp [convolution_def, g]
    rw [hconv]
    have hC : ∀ᵐ s ∂(volume : Measure E),
        eLpNorm (fun x => g (x - s)) (ENNReal.ofReal r) volume ≤
          eLpNorm f (ENNReal.ofReal r) volume :=
      ae_of_all _ fun s => by
        rw [show (fun x => g (x - s)) = g ∘ fun x => x - s from rfl,
          eLpNorm_comp_measurePreserving hf.stronglyMeasurable_mk.aestronglyMeasurable
            (measurePreserving_sub_right volume s), eLpNorm_congr_ae hf.ae_eq_mk.symm]
    calc eLpNorm (fun x => ∫ s, ρ s • g (x - s)) (ENNReal.ofReal r) volume
        ≤ (∫⁻ s, ‖ρ s‖ₑ) * eLpNorm f (ENNReal.ofReal r) volume :=
          eLpNorm_integral_smul_le hr φ.continuous_normed.measurable (F := fun x s => g (x - s))
            (hf.stronglyMeasurable_mk.comp_measurable measurable_sub) hC
      _ = eLpNorm f (ENNReal.ofReal r) volume := by rw [hρ1, one_mul]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Functions supported in a fixed compact set and tending to `0` uniformly tend to `0` in `L^p`. -/
private theorem tendsto_eLpNorm_of_uniform {ι : Type*} {l : Filter ι} {h : ι → E → F} {K : Set E}
    (hK : IsCompact K) (hsupp : ∀ᶠ i in l, Function.support (h i) ⊆ K)
    (hmeas : ∀ i, AEStronglyMeasurable (h i) volume)
    (hunif : ∀ ε > 0, ∀ᶠ i in l, ∀ x, ‖h i x‖ ≤ ε) (p : ℝ≥0∞) :
    Tendsto (fun i => eLpNorm (h i) p volume) l (𝓝 0) := by
  set M := volume K ^ p.toReal⁻¹
  have hM : M ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hK.measure_lt_top.ne
  have hlim : Tendsto (fun ε : ℝ => M * ENNReal.ofReal ε) (𝓝 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ))))
      (Or.inr hM)
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨ε, hεδ, hε⟩ := (((hlim.eventually (ge_mem_nhds hδ)).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
  filter_upwards [hsupp, hunif ε hε] with i hi hbound
  rw [← eLpNorm_restrict_eq_of_support_subset (hmeas i) hi]
  calc eLpNorm (h i) p (volume.restrict K)
      ≤ (volume.restrict K) Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal ε :=
        eLpNorm_le_of_ae_bound (hmeas i).restrict (ae_of_all _ hbound)
    _ = M * ENNReal.ofReal ε := by rw [Measure.restrict_apply_univ]
    _ ≤ δ := hεδ

/-- **Mollification converges in `L^p`**, `1 ≤ p < ∞`: if the radii of the bumps `φ i` tend to `0`,
then `ρ_i ⋆ f → f` in `L^p` for every `f ∈ L^p`. -/
theorem tendsto_eLpNorm_convolution_sub {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : E → F} (hf : MemLp f p volume) :
    Tendsto (fun i => eLpNorm ((φ i).normed volume ⋆[lsmul ℝ ℝ] f - f) p volume) l (𝓝 0) := by
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable hp
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := by simpa using hε.ne'
  -- a continuous `g` with compact support, `‖f − g‖_p ≤ ε / 3`
  obtain ⟨g, hgc, hfg, hgcont, hgp⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp' hε3
  have hgl : LocallyIntegrable g volume := hgcont.locallyIntegrable
  -- `ρ_i ⋆ g → g` uniformly, with supports in the compact `1`-neighbourhood of `tsupport g`
  have hlim : Tendsto (fun i => eLpNorm ((φ i).normed volume ⋆[lsmul ℝ ℝ] g - g) p volume) l
      (𝓝 0) := by
    refine tendsto_eLpNorm_of_uniform (hgc.isCompact.cthickening (r := 1)) ?_ (fun i => ?_)
      (fun δ hδ => ?_) p
    · filter_upwards [hφ.eventually (ge_mem_nhds one_pos)] with i hi x hx
      by_contra hxK
      apply hx
      have hgx : g x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hxK (Metric.self_subset_cthickening _ h)
      have hcx : ((φ i).normed volume ⋆[lsmul ℝ ℝ] g) x = 0 := by
        by_contra hne
        obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset_swap _ hne
        rw [(φ i).support_normed_eq (μ := volume)] at hb
        refine hxK (Metric.mem_cthickening_of_dist_le _ a 1 _ (subset_tsupport _ ha) ?_)
        rw [dist_eq_norm, add_sub_cancel_left]
        exact (mem_ball_zero_iff.1 hb).le.trans hi
      simp [hgx, hcx]
    · exact (((φ i).hasCompactSupport_normed.continuous_convolution_left _
        (φ i).continuous_normed hgl).sub hgcont).aestronglyMeasurable
    · obtain ⟨η, hη, hgη⟩ :=
        Metric.uniformContinuous_iff.1 (hgc.uniformContinuous_of_continuous hgcont) δ hδ
      filter_upwards [hφ.eventually (gt_mem_nhds hη)] with i hi x
      rw [Pi.sub_apply, ← dist_eq_norm]
      exact ContDiffBump.dist_normed_convolution_le hgcont.aestronglyMeasurable
        fun y hy => (hgη ((Metric.mem_ball.1 hy).trans hi)).le
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hlim (ε / 3) (pos_iff_ne_zero.2 hε3)] with i hi
  set ρ := (φ i).normed volume
  have hρc : HasCompactSupport ρ := (φ i).hasCompactSupport_normed
  have hconv : ρ ⋆[lsmul ℝ ℝ] f = ρ ⋆[lsmul ℝ ℝ] (f - g) + ρ ⋆[lsmul ℝ ℝ] g := by
    rw [← ConvolutionExists.distrib_add, sub_add_cancel]
    · exact hρc.convolutionExists_left _ (φ i).continuous_normed (hfl.sub hgl)
    · exact hρc.convolutionExists_left _ (φ i).continuous_normed hgl
  have hsplit : ρ ⋆[lsmul ℝ ℝ] f - f =
      ρ ⋆[lsmul ℝ ℝ] (f - g) + (ρ ⋆[lsmul ℝ ℝ] g - g) + (g - f) := by
    rw [hconv]; abel
  rw [hsplit]
  calc eLpNorm (ρ ⋆[lsmul ℝ ℝ] (f - g) + (ρ ⋆[lsmul ℝ ℝ] g - g) + (g - f)) p volume
      ≤ eLpNorm (ρ ⋆[lsmul ℝ ℝ] (f - g)) p volume + eLpNorm (ρ ⋆[lsmul ℝ ℝ] g - g) p volume +
          eLpNorm (g - f) p volume :=
        (eLpNorm_add_le hp).trans (add_le_add_left (eLpNorm_add_le hp) _)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (eLpNorm_convolution_le (φ i) hp
          (hf.aestronglyMeasurable.sub hgp.aestronglyMeasurable)).trans hfg
        · rw [eLpNorm_sub_comm]; exact hfg
    _ = ε := ENNReal.add_thirds ε

omit [CompleteSpace F] in
/-- **Mollification commutes with weak derivatives**: if `Df` is a weak derivative of `f` on the
whole space, both locally integrable, then `ρ ⋆ f` has the derivative `(ρ ⋆ Df) (x)` at every
`x`. -/
theorem hasFDerivAt_convolution_of_hasWeakFDerivOn (φ : ContDiffBump (0 : E)) {f : E → F}
    {Df : E → E →L[ℝ] F} (hf : LocallyIntegrable f volume) (hDf : LocallyIntegrable Df volume)
    (h : HasWeakFDerivOn Set.univ f Df) (x : E) :
    HasFDerivAt (φ.normed volume ⋆[lsmul ℝ ℝ] f) ((φ.normed volume ⋆[lsmul ℝ ℝ] Df) x) x := by
  set ρ := φ.normed volume
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have hρs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := φ.contDiff_normed
  have hρd : Differentiable ℝ ρ := hρs.differentiable (by simp)
  -- Mathlib: `D (ρ ⋆ f) = (Dρ) ⋆ f`
  refine (hρc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) (hρs.of_le (by exact_mod_cast le_top)) hf
    x).congr_fderiv ?_
  ext v
  have hex₁ : ConvolutionExistsAt (fderiv ℝ ρ) f x ((lsmul ℝ ℝ).precompL E) volume :=
    (hρc.fderiv ℝ).convolutionExists_left _ (hρs.continuous_fderiv (by simp)) hf x
  have hex₂ : ConvolutionExistsAt ρ Df x (lsmul ℝ ℝ) volume :=
    hρc.convolutionExists_left _ φ.continuous_normed hDf x
  rw [convolution_def, convolution_def, ContinuousLinearMap.integral_apply hex₁,
    ContinuousLinearMap.integral_apply hex₂]
  simp only [precompL_apply, lsmul_apply, smul_apply]
  -- the weak derivative, tested against `ψ (y) = ρ (x − y)`
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ρ (x - y)) :=
    hρs.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y => ρ (x - y)) := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have key := h v _ hψ hψc (Set.subset_univ _)
  have hderiv : ∀ y, fderiv ℝ (fun y => ρ (x - y)) y v = -fderiv ℝ ρ (x - y) v := by
    intro y
    have hd : HasFDerivAt (fun y => ρ (x - y))
        ((fderiv ℝ ρ (x - y)).comp (-ContinuousLinearMap.id ℝ E)) y :=
      (hρd (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
    rw [hd.fderiv]
    simp
  simp only [hderiv, neg_smul, integral_neg, neg_inj] at key
  have e₁ := integral_sub_left_eq_self (μ := volume) (fun t => fderiv ℝ ρ t v • f (x - t)) x
  have e₂ := integral_sub_left_eq_self (μ := volume) (fun t => ρ t • Df (x - t) v) x
  simp only [sub_sub_cancel] at e₁ e₂
  rw [← e₁, ← e₂, key]

end HarmonicAnalysis

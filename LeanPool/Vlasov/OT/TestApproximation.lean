/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module

public import LeanPool.Vlasov.OT.CharacteristicFlow
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Compactly supported test approximation for weak Vlasov solutions

Mollification converges together with its first derivative. These estimates extend
the weak equation to compactly supported C¹ tests, independently of flow inversion.
-/

@[expose] public section

namespace Vlasov

open MeasureTheory

variable {d : ℕ} [NeZero d]

open Filter Topology Metric in
open scoped Convolution in
omit [NeZero d] in
/-- Helper 1 — uniform mollification of a continuous, compactly-supported function.
The mollified family `ρ_n ⋆ g` converges to `g` **uniformly** (not just pointwise), the
load-bearing analytic input the `C¹_c` test-class enlargement (#4) needs.  Proof: uniform
continuity of `g` (compact support) gives a single `δ`; once `rOut_n < δ`, the pointwise bump
estimate `dist_normed_convolution_le` fires at *every* base point simultaneously. -/
theorem mollifier_tendstoUniformly {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : PhaseSpace d → E) (hg_cont : Continuous g) (hg_cs : HasCompactSupport g)
    (φ : ℕ → ContDiffBump (0 : PhaseSpace d))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    TendstoUniformly
      (fun n x => ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) g atTop := by
  have hHaar : (volume : Measure (PhaseSpace d)).IsAddHaarMeasure := by
    rw [show (volume : Measure (PhaseSpace d)) = (volume : Measure (PhysSpace d)).prod volume from
      Measure.volume_eq_prod _ _]
    infer_instance
  have hg_uc : UniformContinuous g := hg_cs.uniformContinuous_of_continuous hg_cont
  rw [Metric.uniformContinuous_iff] at hg_uc
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ_prop⟩ := hg_uc (ε / 2) (by positivity)
  have hev : ∀ᶠ n in atTop, (φ n).rOut < δ := hφ.eventually (Iio_mem_nhds hδ)
  filter_upwards [hev] with n hn
  intro x₀
  rw [dist_comm]
  have hball : ∀ x ∈ ball x₀ (φ n).rOut, dist (g x) (g x₀) ≤ ε / 2 := by
    intro x hx
    exact le_of_lt (hδ_prop (lt_trans (mem_ball.mp hx) hn))
  have hbump := ContDiffBump.dist_normed_convolution_le (μ := volume) (φ := φ n) (g := g)
    hg_cont.aestronglyMeasurable hball
  exact lt_of_le_of_lt hbump (half_lt_self hε)

open Filter Topology Metric in
open scoped Convolution in
omit [NeZero d] in
/-- Helper 2 — the mollified Fréchet derivative converges uniformly.
`fderiv (ρ_n ⋆ χ) = ρ_n ⋆ (fderiv χ)` (convolution commutes onto the `C¹` factor via
`HasCompactSupport.hasFDerivAt_convolution_right`, with `precompR` reconciled to `lsmul` on the
operator codomain), and the right-hand side converges uniformly to `fderiv χ` by Helper 1 applied
to the continuous, compactly-supported `fderiv χ`. -/
theorem mollifiedFDeriv_tendstoUniformly
    (χ : PhaseSpace d → ℝ) (hχ_C1 : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (φ : ℕ → ContDiffBump (0 : PhaseSpace d))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    TendstoUniformly
      (fun n z => fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ) z)
      (fderiv ℝ χ) atTop := by
  have hHaar : (volume : Measure (PhaseSpace d)).IsAddHaarMeasure := by
    rw [show (volume : Measure (PhaseSpace d)) = (volume : Measure (PhysSpace d)).prod volume from
      Measure.volume_eq_prod _ _]
    infer_instance
  have hdf_cont : Continuous (fderiv ℝ χ) := hχ_C1.continuous_fderiv one_ne_zero
  have hdf_cs : HasCompactSupport (fderiv ℝ χ) := hχc.fderiv ℝ
  -- the `precompR` bilinear map coincides with `lsmul` on the operator codomain
  have hbridge : (ContinuousLinearMap.lsmul ℝ ℝ).precompR (PhaseSpace d)
      = (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (PhaseSpace d →L[ℝ] ℝ) →L[ℝ] (PhaseSpace d →L[ℝ] ℝ)) := by
    refine ContinuousLinearMap.ext fun u => ?_
    refine ContinuousLinearMap.ext fun v => ?_
    refine ContinuousLinearMap.ext fun x => ?_
    simp [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.lsmul_apply]
  have hfd : ∀ n, (fun z => fderiv ℝ
        ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ) z)
      = (fun z => ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ χ) z) := by
    intro n
    funext z
    rw [(hχc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
      ((φ n).continuous_normed.locallyIntegrable) hχ_C1 z).fderiv, hbridge]
  have hgoal_eq :
      (fun n z => fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ) z)
      = (fun n z =>
          ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ χ) z) := by
    funext n; exact hfd n
  rw [hgoal_eq]
  exact mollifier_tendstoUniformly (fderiv ℝ χ) hdf_cont hdf_cs φ hφ

-- ── Helpers for `weakEvolution_test_C1c_On`, extracted from its proof body (the
--    mathematical content is unchanged; each piece is generic in the test function). ──

omit [NeZero d] in
/-- Norm bound for the dual-composed difference of two Fréchet derivatives. -/
lemma toDualSymm_comp_sub_norm_le (ψ ϕ : PhaseSpace d → ℝ)
    (z : PhaseSpace d) (e : PhysSpace d →L[ℝ] PhaseSpace d) :
    ‖(InnerProductSpace.toDual ℝ (PhysSpace d)).symm ((fderiv ℝ ψ z).comp e)
      - (InnerProductSpace.toDual ℝ (PhysSpace d)).symm ((fderiv ℝ ϕ z).comp e)‖
    ≤ ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ * ‖e‖ := by
  rw [← map_sub, LinearIsometryEquiv.norm_map, ← ContinuousLinearMap.sub_comp]
  exact ContinuousLinearMap.opNorm_comp_le _ _

omit [NeZero d] in
/-- Chain rule: the Fréchet derivative of an `x`-slice is the composition with `inl`. -/
lemma fderiv_slice_fst (ψ : PhaseSpace d → ℝ) (hψ : Differentiable ℝ ψ) (z : PhaseSpace d) :
    fderiv ℝ (fun x => ψ (x, z.2)) z.1
      = (fderiv ℝ ψ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) := by
  have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
      (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
    hasFDerivAt_prodMk_left z.1 z.2
  exact ((hψ z).hasFDerivAt.comp z.1 h2).fderiv

omit [NeZero d] in
/-- Chain rule: the Fréchet derivative of a `v`-slice is the composition with `inr`. -/
lemma fderiv_slice_snd (ψ : PhaseSpace d → ℝ) (hψ : Differentiable ℝ ψ) (z : PhaseSpace d) :
    fderiv ℝ (fun v => ψ (z.1, v)) z.2
      = (fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
  have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
      (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  exact ((hψ z).hasFDerivAt.comp z.2 h2).fderiv

omit [NeZero d] in
/-- Continuity of the first-slot partial-gradient field of a `C¹` test function. -/
lemma continuous_gradientSlice_fst (ψ : PhaseSpace d → ℝ) (g : PhaseSpace d → PhysSpace d)
    (hψ : Differentiable ℝ ψ) (hψ' : Continuous (fderiv ℝ ψ))
    (hg : ∀ z, g z = gradient (fun x => ψ (x, z.2)) z.1) : Continuous g := by
  have heq : g = fun z => (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))) := by
    funext z; rw [hg z]; simp only [gradient]; rw [fderiv_slice_fst ψ hψ z]
  rw [heq]
  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
    (hψ'.clm_comp continuous_const)

omit [NeZero d] in
/-- Continuity of the second-slot partial-gradient field of a `C¹` test function. -/
lemma continuous_gradientSlice_snd (ψ : PhaseSpace d → ℝ) (g : PhaseSpace d → PhysSpace d)
    (hψ : Differentiable ℝ ψ) (hψ' : Continuous (fderiv ℝ ψ))
    (hg : ∀ z, g z = gradient (fun v => ψ (z.1, v)) z.2) : Continuous g := by
  have heq : g = fun z => (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))) := by
    funext z; rw [hg z]; simp only [gradient]; rw [fderiv_slice_snd ψ hψ z]
  rw [heq]
  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
    (hψ'.clm_comp continuous_const)

omit [NeZero d] in
/-- Compact support of the first-slot partial-gradient field. -/
lemma hasCompactSupport_gradientSlice_fst (ψ : PhaseSpace d → ℝ)
    (g : PhaseSpace d → PhysSpace d) (hψ : Differentiable ℝ ψ) (hψcs : HasCompactSupport ψ)
    (hg : ∀ z, g z = gradient (fun x => ψ (x, z.2)) z.1) : HasCompactSupport g := by
  apply HasCompactSupport.intro hψcs
  intro z hz
  have hf0 : fderiv ℝ ψ z = 0 := fderiv_of_notMem_tsupport ℝ hz
  rw [hg z]; simp only [gradient]; rw [fderiv_slice_fst ψ hψ z, hf0]; simp

omit [NeZero d] in
/-- Compact support of the second-slot partial-gradient field. -/
lemma hasCompactSupport_gradientSlice_snd (ψ : PhaseSpace d → ℝ)
    (g : PhaseSpace d → PhysSpace d) (hψ : Differentiable ℝ ψ) (hψcs : HasCompactSupport ψ)
    (hg : ∀ z, g z = gradient (fun v => ψ (z.1, v)) z.2) : HasCompactSupport g := by
  apply HasCompactSupport.intro hψcs
  intro z hz
  have hf0 : fderiv ℝ ψ z = 0 := fderiv_of_notMem_tsupport ℝ hz
  rw [hg z]; simp only [gradient]; rw [fderiv_slice_snd ψ hψ z, hf0]; simp

omit [NeZero d] in
/-- First-slot partial gradients of two tests differ by at most the full
Fréchet-derivative difference. -/
lemma gradientSlice_fst_sub_norm_le (ψ ϕ : PhaseSpace d → ℝ)
    (hψ : Differentiable ℝ ψ) (hϕ : Differentiable ℝ ϕ)
    (gψ gϕ : PhaseSpace d → PhysSpace d)
    (hgψ : ∀ z, gψ z = gradient (fun x => ψ (x, z.2)) z.1)
    (hgϕ : ∀ z, gϕ z = gradient (fun x => ϕ (x, z.2)) z.1) (z : PhaseSpace d) :
    ‖gψ z - gϕ z‖ ≤ ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ := by
  have e1 : gψ z = (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))) := by
    rw [hgψ z]; simp only [gradient]; rw [fderiv_slice_fst ψ hψ z]
  have e2 : gϕ z = (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ϕ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))) := by
    rw [hgϕ z]; simp only [gradient]; rw [fderiv_slice_fst ϕ hϕ z]
  rw [e1, e2]
  refine le_trans (toDualSymm_comp_sub_norm_le ψ ϕ z _) ?_
  calc ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ * ‖ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)‖
      ≤ ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ * 1 := by
        gcongr; exact ContinuousLinearMap.norm_inl_le_one ℝ (PhysSpace d) (PhysSpace d)
    _ = ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ := mul_one _

omit [NeZero d] in
/-- Second-slot partial gradients of two tests differ by at most the full
Fréchet-derivative difference. -/
lemma gradientSlice_snd_sub_norm_le (ψ ϕ : PhaseSpace d → ℝ)
    (hψ : Differentiable ℝ ψ) (hϕ : Differentiable ℝ ϕ)
    (gψ gϕ : PhaseSpace d → PhysSpace d)
    (hgψ : ∀ z, gψ z = gradient (fun v => ψ (z.1, v)) z.2)
    (hgϕ : ∀ z, gϕ z = gradient (fun v => ϕ (z.1, v)) z.2) (z : PhaseSpace d) :
    ‖gψ z - gϕ z‖ ≤ ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ := by
  have e1 : gψ z = (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))) := by
    rw [hgψ z]; simp only [gradient]; rw [fderiv_slice_snd ψ hψ z]
  have e2 : gϕ z = (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ϕ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))) := by
    rw [hgϕ z]; simp only [gradient]; rw [fderiv_slice_snd ϕ hϕ z]
  rw [e1, e2]
  refine le_trans (toDualSymm_comp_sub_norm_le ψ ϕ z _) ?_
  calc ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ * ‖ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)‖
      ≤ ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ * 1 := by
        gcongr; exact ContinuousLinearMap.norm_inr_le_one ℝ (PhysSpace d) (PhysSpace d)
    _ = ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ := mul_one _

omit [NeZero d] in
/-- Integrability of the weak-evolution integrand against a probability measure:
continuous with compact support (both gradient slots), continuous field. -/
lemma inner_integrand_integrable
    (μ : Measure (PhaseSpace d)) [IsProbabilityMeasure μ]
    (fld : PhysSpace d → PhysSpace d) (hfld : Continuous fld)
    (gX gV : PhaseSpace d → PhysSpace d)
    (hgXc : Continuous gX) (hgVc : Continuous gV)
    (hgXcs : HasCompactSupport gX) (hgVcs : HasCompactSupport gV) :
    Integrable (fun z => @inner ℝ (PhysSpace d) _ z.2 (gX z)
      - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z)) μ := by
  have hcont : Continuous (fun z => @inner ℝ (PhysSpace d) _ z.2 (gX z)
      - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z)) :=
    (continuous_snd.inner hgXc).sub ((hfld.comp continuous_fst).inner hgVc)
  have hcs : HasCompactSupport (fun z => @inner ℝ (PhysSpace d) _ z.2 (gX z)
      - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z)) := by
    apply HasCompactSupport.intro (IsCompact.union hgXcs hgVcs)
    intro z hz
    simp only [Set.mem_union, not_or] at hz
    rw [image_eq_zero_of_notMem_tsupport hz.1, image_eq_zero_of_notMem_tsupport hz.2]
    simp
  exact hcont.integrable_of_hasCompactSupport hcs

omit [NeZero d] in
/-- Pointwise bound on the difference of two weak-evolution integrands: on the
common support `K` it is `(R_K + B) * δ` (norm bound `R_K` on `K`, field bound `B`
on `K`, gradient-slot distance `δ`); off `K` both integrands agree. -/
lemma inner_integrand_sub_norm_le
    (K : Set (PhaseSpace d)) (R_K : ℝ) (hR_K_nn : 0 ≤ R_K) (hR_K : ∀ z ∈ K, ‖z‖ ≤ R_K)
    (fld : PhysSpace d → PhysSpace d) (B : ℝ) (hB_nn : 0 ≤ B)
    (hfld_K : ∀ z ∈ K, ‖fld (Prod.fst z)‖ ≤ B)
    (gX gV gX' gV' : PhaseSpace d → PhysSpace d) (δ : ℝ) (hδ_nn : 0 ≤ δ)
    (hXd : ∀ z, ‖gX' z - gX z‖ ≤ δ) (hVd : ∀ z, ‖gV' z - gV z‖ ≤ δ)
    (hXoff : ∀ z ∉ K, gX' z = gX z) (hVoff : ∀ z ∉ K, gV' z = gV z)
    (z : PhaseSpace d) :
    ‖(@inner ℝ (PhysSpace d) _ z.2 (gX z) - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z))
      - (@inner ℝ (PhysSpace d) _ z.2 (gX' z)
          - @inner ℝ (PhysSpace d) _ (fld z.1) (gV' z))‖
    ≤ (R_K + B) * δ := by
  by_cases hzK : z ∈ K
  · have hrw : (@inner ℝ (PhysSpace d) _ z.2 (gX z)
          - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z))
        - (@inner ℝ (PhysSpace d) _ z.2 (gX' z)
          - @inner ℝ (PhysSpace d) _ (fld z.1) (gV' z))
        = @inner ℝ (PhysSpace d) _ z.2 (gX z - gX' z)
          - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z - gV' z) := by
      rw [inner_sub_right, inner_sub_right]; ring
    rw [Real.norm_eq_abs, hrw]
    have hb1 : |@inner ℝ (PhysSpace d) _ z.2 (gX z - gX' z)| ≤ R_K * δ := by
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      have hz2 : ‖z.2‖ ≤ R_K := le_trans (norm_snd_le z) (hR_K z hzK)
      rw [norm_sub_rev (gX z)]
      exact mul_le_mul hz2 (hXd z) (norm_nonneg _) hR_K_nn
    have hb2 : |@inner ℝ (PhysSpace d) _ (fld z.1) (gV z - gV' z)| ≤ B * δ := by
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      rw [norm_sub_rev (gV z)]
      exact mul_le_mul (hfld_K z hzK) (hVd z) (norm_nonneg _) hB_nn
    calc |@inner ℝ (PhysSpace d) _ z.2 (gX z - gX' z)
            - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z - gV' z)|
        ≤ |@inner ℝ (PhysSpace d) _ z.2 (gX z - gX' z)|
          + |@inner ℝ (PhysSpace d) _ (fld z.1) (gV z - gV' z)| := abs_sub _ _
      _ ≤ R_K * δ + B * δ := by linarith
      _ = (R_K + B) * δ := by ring
  · rw [hXoff z hzK, hVoff z hzK]
    simp only [sub_self, norm_zero]
    positivity

omit [NeZero d] in
/-- On the window, the frozen convolution field over the spatial marginal is
integrable (in force form), linearly bounded, and continuous — packaged for
consumers that quantify over the window. -/
lemma convolveField_window_setup
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (M_ρ : ℝ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (ε₀ : ℝ) (hε₀_def : ε₀ = ‖gradW 0‖ + (L : ℝ) * M_ρ) :
    ∀ σ ∈ Set.Icc (0 : ℝ) T,
      (Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f σ)))
      ∧ (∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) (spatialMarginal (f σ)))
      ∧ (∀ x : PhysSpace d,
          ‖convolveFunctionMeasure gradW (spatialMarginal (f σ)) x‖ ≤ ε₀ + (L:ℝ) * ‖x‖)
      ∧ Continuous (fun x => convolveFunctionMeasure gradW (spatialMarginal (f σ)) x) := by
  intro σ hσ
  have : IsProbabilityMeasure (f σ) := (hf_mom σ hσ).1
  have hprob_m : IsProbabilityMeasure (spatialMarginal (f σ)) :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  -- ‖·‖ integrable wrt the spatial marginal (from the finite first moment of f σ)
  have h_y_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f σ)) := by
    unfold spatialMarginal
    rw [integrable_map_measure (continuous_norm.measurable).aestronglyMeasurable
      measurable_fst.aemeasurable]
    refine Integrable.mono' (hf_mom σ hσ).2
      ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    change |‖z.1‖| ≤ ‖z‖
    rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z
  -- force-integrability (Lipschitz growth + finite moment)
  have h_int : ∀ x : PhysSpace d,
      Integrable (fun y => gradW (x - y)) (spatialMarginal (f σ)) := by
    intro x
    have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x - y))
        (spatialMarginal (f σ)) :=
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have h_dom : ∀ y : PhysSpace d,
        ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L:ℝ) * ‖x‖ + (L:ℝ) * ‖y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      have h_sub_le : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
      linarith
    have h_dom_int : Integrable
        (fun y : PhysSpace d => ‖gradW 0‖ + (L:ℝ) * ‖x‖ + (L:ℝ) * ‖y‖)
        (spatialMarginal (f σ)) := by
      have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L:ℝ) * ‖x‖ + (L:ℝ) * ‖y‖)
          = fun y => (‖gradW 0‖ + (L:ℝ) * ‖x‖) + (L:ℝ) * ‖y‖ := by funext y; ring
      rw [h_eq]; exact (integrable_const _).add (h_y_int.const_mul _)
    exact Integrable.mono' h_dom_int h_aesm (Filter.Eventually.of_forall h_dom)
  -- field bound (CharFlow idiom)
  have hbound : ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (spatialMarginal (f σ)) x‖ ≤ ε₀ + (L:ℝ) * ‖x‖ := by
    intro x
    rw [hε₀_def]
    exact norm_convolveFunctionMeasure_le_affine gradW L hL (spatialMarginal (f σ))
      h_int h_y_int M_ρ (hM_ρ σ hσ) x
  -- field continuity from the Lipschitz-in-x lemma
  have hcont : Continuous (fun x => convolveFunctionMeasure gradW (spatialMarginal (f σ)) x) :=
    (convolveFunctionMeasure_lipschitz_in_x gradW L hL (spatialMarginal (f σ)) h_int).continuous
  exact ⟨h_y_int, h_int, hbound, hcont⟩

omit [NeZero d] in
open Filter Topology Metric in
/-- Uniform convergence of integrands implies convergence of the integrals against
a probability measure (every term integrable). -/
lemma integral_tendsto_of_tendstoUniformly
    (μ : Measure (PhaseSpace d)) [IsProbabilityMeasure μ]
    (g : ℕ → PhaseSpace d → ℝ) (g₀ : PhaseSpace d → ℝ)
    (hUnif : TendstoUniformly g g₀ atTop)
    (hg₀_int : Integrable g₀ μ) (hg_int : ∀ n, Integrable (g n) μ) :
    Tendsto (fun n => ∫ z, g n z ∂μ) atTop (𝓝 (∫ z, g₀ z ∂μ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformly_iff.mp hUnif (ε/2) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have hpt : ∀ z, |g n z - g₀ z| ≤ ε/2 := by
    intro z
    have h := hN n hn z
    rw [Real.dist_eq, abs_sub_comm] at h
    exact le_of_lt h
  calc |∫ z, g n z ∂μ - ∫ z, g₀ z ∂μ|
      = |∫ z, (g n z - g₀ z) ∂μ| := by rw [integral_sub (hg_int n) hg₀_int]
    _ ≤ ∫ z, |g n z - g₀ z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _z, (ε/2) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
          (integrable_const _) (Eventually.of_forall hpt)
    _ = ε/2 := by simp
    _ < ε := half_lt_self hε

-- #4 (Step 5 interface): the weak evolution equation extended to C¹_c test functions.
open Filter Topology Metric in
open scoped Convolution Pointwise in
omit [NeZero d] in
theorem weakEvolution_test_C1c_On
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    -- B2 enrichment (mollification proof): the velocity-term needs a uniform-in-σ bound on the
    -- frozen field `‖∇W∗ρ_σ‖` over the fixed compact support of the test, supplied by the
    -- Lipschitz growth of `gradW` (`hL`) and the uniform first-moment bound `hM_ρ`.
    (L : NNReal) (hL : LipschitzWith L gradW)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (χ : PhaseSpace d → ℝ) (hχ_C1 : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (gradXχ gradVχ : PhaseSpace d → PhysSpace d)
    (hgradXχ : ∀ z, gradXχ z = gradient (fun x => χ (x, z.2)) z.1)
    (hgradVχ : ∀ z, gradVχ z = gradient (fun v => χ (z.1, v)) z.2)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun σ => ∫ z, χ z ∂(f σ))
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXχ z)
             - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f s)) z.1)
                (gradVχ z)) ∂(f s)) s := by
  classical
  have hHaar : (volume : Measure (PhaseSpace d)).IsAddHaarMeasure := by
    rw [show (volume : Measure (PhaseSpace d)) = (volume : Measure (PhysSpace d)).prod volume from
      Measure.volume_eq_prod _ _]
    infer_instance
  have hvolReg : (volume : Measure (PhaseSpace d)).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  -- mollifier family (shrinking bumps); copy of #9's
  set φ : ℕ → ContDiffBump (0 : PhaseSpace d) :=
    fun n => ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ_def
  have hrout : ∀ n, (φ n).rOut = 2 / (n + 2) := fun n => rfl
  have hrout_tendsto : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    simp only [hrout]
    apply Filter.Tendsto.div_atTop (tendsto_const_nhds)
    exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  -- mollified test functions
  set χn : ℕ → PhaseSpace d → ℝ :=
    fun n => (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ with hχn_def
  have hχn_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (χn n) := fun n =>
    ((φ n).hasCompactSupport_normed).contDiff_convolution_left _
      (φ n).contDiff_normed hχ_C1.continuous.locallyIntegrable
  have hχn_cs : ∀ n, HasCompactSupport (χn n) := fun n =>
    HasCompactSupport.convolution _ (φ n).hasCompactSupport_normed hχc
  -- genuine partial gradients of χ_n
  set gXn : ℕ → PhaseSpace d → PhysSpace d :=
    fun n z => gradient (fun x => χn n (x, z.2)) z.1 with hgXn_def
  set gVn : ℕ → PhaseSpace d → PhysSpace d :=
    fun n z => gradient (fun v => χn n (z.1, v)) z.2 with hgVn_def
  -- D_n: the C^∞ weak-evolution derivative, from hf_weak applied to χ_n
  have hDn : ∀ n, ∀ σ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (fun σ' => ∫ z, χn n z ∂(f σ'))
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gXn n z)
             - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f σ)) z.1)
                (gVn n z)) ∂(f σ)) σ := by
    intro n σ hσ
    have h := hf_weak (χn n) (hχn_smooth n) (hχn_cs n) (gXn n) (gVn n)
      (fun z => rfl) (fun z => rfl) σ hσ
    simpa using h
  -- pointwise convergence (0th order): ∫ χ_n d(f σ) → ∫ χ d(f σ)
  have hfg : ∀ σ ∈ Set.Ioo (0 : ℝ) T, Tendsto (fun n => ∫ z, χn n z ∂(f σ)) atTop
      (𝓝 (∫ z, χ z ∂(f σ))) := by
    intro σ hσ
    have : IsProbabilityMeasure (f σ) := (hf_mom σ (Set.Ioo_subset_Icc_self hσ)).1
    exact integral_tendsto_of_tendstoUniformly (f σ) χn χ
      (mollifier_tendstoUniformly χ hχ_C1.continuous hχc φ hrout_tendsto)
      (hχ_C1.continuous.integrable_of_hasCompactSupport hχc)
      (fun n => (hχn_smooth n).continuous.integrable_of_hasCompactSupport (hχn_cs n))
  -- uniform-in-σ convergence of the derivatives (the term bound)
  -- Helper 2: uniform fderiv convergence
  have hH2 := mollifiedFDeriv_tendstoUniformly χ hχ_C1 hχc φ hrout_tendsto
  -- fixed compact K containing all supports
  set K : Set (PhaseSpace d) := tsupport χ + Metric.closedBall (0 : PhaseSpace d) 1 with hK_def
  have hK_compact : IsCompact K := IsCompact.add hχc (isCompact_closedBall 0 1)
  obtain ⟨R0, hR0⟩ := (hK_compact.image continuous_norm).bddAbove
  set R_K := max R0 0 with hRK_def
  have hR_K_nn : (0 : ℝ) ≤ R_K := le_max_right _ _
  have hR_K : ∀ z ∈ K, ‖z‖ ≤ R_K := fun z hz => le_trans (hR0 ⟨z, hz, rfl⟩) (le_max_left _ _)
  -- tsupport χ ⊆ K, and fderiv χ vanishes off K
  have htsuppχ_K : tsupport χ ⊆ K := by
    intro z hz
    rw [hK_def]
    exact (add_zero z) ▸ Set.add_mem_add hz (by simp : (0:PhaseSpace d) ∈ Metric.closedBall 0 1)
  have hsuppχ : ∀ z ∉ K, fderiv ℝ χ z = 0 := by
    intro z hz
    exact fderiv_of_notMem_tsupport ℝ (fun h => hz (htsuppχ_K h))
  -- tsupport (χn n) ⊆ K, and fderiv (χn n) vanishes off K
  have htsuppχn_K : ∀ n, tsupport (χn n) ⊆ K := by
    intro n
    have h1 : Function.support (χn n)
        ⊆ Function.support ((φ n).normed volume) + Function.support χ :=
      support_convolution_subset _
    have h2 : Function.support ((φ n).normed volume) ⊆ Metric.closedBall 0 1 := by
      rw [(φ n).support_normed_eq]
      refine Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ?_)
      rw [hrout n]; rw [div_le_one (by positivity)]; norm_num
    have h4 : Function.support (χn n) ⊆ K := by
      refine h1.trans ?_
      rw [hK_def, add_comm (tsupport χ)]
      exact Set.add_subset_add h2 (subset_tsupport χ)
    exact (closure_minimal h4 hK_compact.isClosed)
  have hsuppχn : ∀ n, ∀ z ∉ K, fderiv ℝ (χn n) z = 0 := by
    intro n z hz
    exact fderiv_of_notMem_tsupport ℝ (fun h => hz (htsuppχn_K n h))
  -- partial-gradient projection bounds (X and V), off Helper 2's fderiv difference
  -- field: integrability, bound, continuity — all on the window
  set ε₀ : ℝ := ‖gradW 0‖ + (L : ℝ) * M_ρ with hε₀_def
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  have hfield_setup := convolveField_window_setup gradW L hL f T hf_mom M_ρ hM_ρ ε₀ hε₀_def
  -- THE ESTIMATE
  -- continuity of the four partial gradients (off the uniform fderiv)
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hχdiff : Differentiable ℝ χ := hχ_C1.differentiable one_ne_zero
  have hχ'cont : Continuous (fderiv ℝ χ) := hχ_C1.continuous_fderiv one_ne_zero
  have hgXχc : Continuous gradXχ :=
    continuous_gradientSlice_fst χ gradXχ hχdiff hχ'cont hgradXχ
  have hgVχc : Continuous gradVχ :=
    continuous_gradientSlice_snd χ gradVχ hχdiff hχ'cont hgradVχ
  have hgXnc : ∀ n, Continuous (gXn n) := fun n => continuous_gradientSlice_fst (χn n) (gXn n)
    ((hχn_smooth n).differentiable htop) ((hχn_smooth n).continuous_fderiv htop)
    (fun z => by rw [hgXn_def])
  have hgVnc : ∀ n, Continuous (gVn n) := fun n => continuous_gradientSlice_snd (χn n) (gVn n)
    ((hχn_smooth n).differentiable htop) ((hχn_smooth n).continuous_fderiv htop)
    (fun z => by rw [hgVn_def])
  -- compact support of the four partial gradients (vanish off the test's support)
  have hgXχcs : HasCompactSupport gradXχ :=
    hasCompactSupport_gradientSlice_fst χ gradXχ hχdiff hχc hgradXχ
  have hgVχcs : HasCompactSupport gradVχ :=
    hasCompactSupport_gradientSlice_snd χ gradVχ hχdiff hχc hgradVχ
  have hgXncs : ∀ n, HasCompactSupport (gXn n) := fun n =>
    hasCompactSupport_gradientSlice_fst (χn n) (gXn n)
      ((hχn_smooth n).differentiable htop) (hχn_cs n) (fun z => by rw [hgXn_def])
  have hgVncs : ∀ n, HasCompactSupport (gVn n) := fun n =>
    hasCompactSupport_gradientSlice_snd (χn n) (gVn n)
      ((hχn_smooth n).differentiable htop) (hχn_cs n) (fun z => by rw [hgVn_def])
  -- THE ESTIMATE
  have hf'unif : TendstoUniformlyOn
      (fun n σ => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gXn n z)
             - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f σ)) z.1) (gVn n z)) ∂(f σ))
      (fun σ => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXχ z)
             - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f σ)) z.1) (gradVχ z)) ∂(f σ))
      atTop (Set.Ioo 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set C : ℝ := R_K + (ε₀ + (L:ℝ) * R_K) with hC_def
    have hC_nn : (0 : ℝ) ≤ C := by rw [hC_def]; positivity
    rw [Metric.tendstoUniformly_iff] at hH2
    filter_upwards [hH2 (ε/(C+1)) (by positivity)] with n hn
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self hσ
    have : IsProbabilityMeasure (f σ) := (hf_mom σ hσ').1
    obtain ⟨_, _, hbnd, hfc⟩ := hfield_setup σ hσ'
    -- L15: make the field opaque so defeq never unfolds its Bochner integral
    set fldσ : PhysSpace d → PhysSpace d := convolveFunctionMeasure gradW (spatialMarginal (f σ))
      with hfldσ_def
    clear_value fldσ
    -- projection bounds for this n
    have hXp : ∀ z, ‖gXn n z - gradXχ z‖ ≤ ‖fderiv ℝ (χn n) z - fderiv ℝ χ z‖ :=
      fun z => gradientSlice_fst_sub_norm_le (χn n) χ
        ((hχn_smooth n).differentiable htop) hχdiff (gXn n) gradXχ
        (fun z => by rw [hgXn_def]) hgradXχ z
    have hVp : ∀ z, ‖gVn n z - gradVχ z‖ ≤ ‖fderiv ℝ (χn n) z - fderiv ℝ χ z‖ :=
      fun z => gradientSlice_snd_sub_norm_le (χn n) χ
        ((hχn_smooth n).differentiable htop) hχdiff (gVn n) gradVχ
        (fun z => by rw [hgVn_def]) hgradVχ z
    -- uniform fderiv bound at this n (uses χn = the convolution defeq, before clearing)
    have hfd_le : ∀ z, ‖fderiv ℝ (χn n) z - fderiv ℝ χ z‖ ≤ ε/(C+1) := by
      intro z
      have h := hn z
      rw [dist_eq_norm, norm_sub_rev] at h
      exact le_of_lt h
    -- L15: with the projection + fderiv bounds proven, make the heavy convolution defs opaque so
    -- the integrand-difference manipulations never unfold their Bochner integrals
    clear_value gXn gVn χn
    -- off K both gradient pairs agree (fderivs vanish there)
    have hXoff : ∀ z ∉ K, gXn n z = gradXχ z := by
      intro z hzK
      have hfd0 : fderiv ℝ (χn n) z = 0 := hsuppχn n z hzK
      have hfd0' : fderiv ℝ χ z = 0 := hsuppχ z hzK
      have := hXp z; rw [hfd0, hfd0', sub_self, norm_zero] at this
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    have hVoff : ∀ z ∉ K, gVn n z = gradVχ z := by
      intro z hzK
      have hfd0 : fderiv ℝ (χn n) z = 0 := hsuppχn n z hzK
      have hfd0' : fderiv ℝ χ z = 0 := hsuppχ z hzK
      have := hVp z; rw [hfd0, hfd0', sub_self, norm_zero] at this
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    -- field bound on K
    have hfld_K : ∀ z ∈ K, ‖fldσ (Prod.fst z)‖ ≤ ε₀ + (L:ℝ) * R_K := by
      intro z hzK
      refine le_trans (hbnd z.1) ?_
      have : ‖z.1‖ ≤ R_K := le_trans (norm_fst_le z) (hR_K z hzK)
      gcongr
    -- pointwise bound on the integrand difference
    have hpt : ∀ z, ‖(@inner ℝ (PhysSpace d) _ z.2 (gradXχ z)
          - @inner ℝ (PhysSpace d) _ (fldσ z.1)
              (gradVχ z))
        - (@inner ℝ (PhysSpace d) _ z.2 (gXn n z)
          - @inner ℝ (PhysSpace d) _ (fldσ z.1)
              (gVn n z))‖ ≤ C * (ε/(C+1)) := by
      intro z
      have h := inner_integrand_sub_norm_le K R_K hR_K_nn hR_K fldσ
        (ε₀ + (L:ℝ) * R_K) (by positivity) hfld_K
        gradXχ gradVχ (gXn n) (gVn n) (ε/(C+1)) (by positivity)
        (fun z => le_trans (hXp z) (hfd_le z)) (fun z => le_trans (hVp z) (hfd_le z))
        hXoff hVoff z
      refine le_trans h (le_of_eq ?_)
      rw [hC_def]
    -- integrability of both integrands (continuous + compact support in K)
    have hGd_int := inner_integrand_integrable (f σ) fldσ hfc gradXχ gradVχ
      hgXχc hgVχc hgXχcs hgVχcs
    have hGnd_int := inner_integrand_integrable (f σ) fldσ hfc (gXn n) (gVn n)
      (hgXnc n) (hgVnc n) (hgXncs n) (hgVncs n)
    -- assemble
    rw [Real.dist_eq, ← integral_sub hGd_int hGnd_int]
    calc |∫ z, ((@inner ℝ (PhysSpace d) _ z.2 (gradXχ z)
            - @inner ℝ (PhysSpace d) _ (fldσ z.1)
                (gradVχ z))
          - (@inner ℝ (PhysSpace d) _ z.2 (gXn n z)
            - @inner ℝ (PhysSpace d) _ (fldσ z.1)
                (gVn n z))) ∂(f σ)|
        ≤ ∫ z, C * (ε/(C+1)) ∂(f σ) := by
          refine le_trans (abs_integral_le_integral_abs) ?_
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun z => ?_)
          have := hpt z; rwa [Real.norm_eq_abs] at this
      _ = C * (ε/(C+1)) := by simp
      _ < ε := by
          have h1 : (0 : ℝ) < C + 1 := by positivity
          rw [← mul_div_assoc, div_lt_iff₀ h1]
          nlinarith [hε, hC_nn]
  -- assemble via the uniform-limit-of-derivatives theorem
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hf'unif (Eventually.of_forall hDn) hfg hs

-- NC (consumption form): integral of a jointly-continuous, uniformly-compactly-supported
-- family against the weak-solution measure curve is continuous in time.
omit [NeZero d] in
theorem vlasovSolutionOn_integral_continuousOn
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (G : ℝ → PhaseSpace d → ℝ)
    (hG_cont : Continuous (fun p : ℝ × PhaseSpace d => G p.1 p.2))
    (K : Set (PhaseSpace d)) (hK : IsCompact K)
    (hG_supp : ∀ s, ∀ z ∉ K, G s z = 0) :
    ContinuousOn (fun s => ∫ z, G s z ∂(f s)) (Set.Icc (0 : ℝ) T) := by
  -- Each slice G a is continuous, supported in K, hence integrable wrt the probability f b.
  have hGs_cont : ∀ a : ℝ, Continuous (fun z => G a z) := fun a =>
    hG_cont.comp (Continuous.prodMk_right a)
  have hGs_cs : ∀ a : ℝ, HasCompactSupport (fun z => G a z) := by
    intro a
    have hsub : tsupport (fun z => G a z) ⊆ K :=
      closure_minimal (fun z hz => by by_contra hzK; exact hz (hG_supp a z hzK)) hK.isClosed
    exact IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hsub
  have hGint : ∀ (a b : ℝ), b ∈ Set.Icc (0 : ℝ) T → Integrable (fun z => G a z) (f b) := by
    intro a b hb
    have := (hf_mom b hb).1
    exact (hGs_cont a).integrable_of_hasCompactSupport (hGs_cs a)
  -- Uniform continuity of the uncurried G on the compact Icc 0 T ×ˢ K.
  have hC : IsCompact (Set.Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  have hG_uc : UniformContinuousOn (fun p : ℝ × PhaseSpace d => G p.1 p.2)
      (Set.Icc (0 : ℝ) T ×ˢ K) :=
    hC.uniformContinuousOn_of_continuous hG_cont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hG_uc
  -- Main ε–δ.
  rw [Metric.continuousOn_iff]
  intro s₀ hs₀ ε hε
  obtain ⟨δ₁, hδ₁, hδ₁_prop⟩ := hG_uc (ε/2) (by positivity)
  -- term2: narrow continuity of f tested against the frozen g := G s₀.
  have hterm2 : ContinuousWithinAt (fun s => ∫ z, G s₀ z ∂(f s)) (Set.Icc 0 T) s₀ :=
    (hf_narrow (fun z => G s₀ z) (hGs_cont s₀) (hGs_cs s₀)) s₀ hs₀
  rw [Metric.continuousWithinAt_iff] at hterm2
  obtain ⟨δ₂, hδ₂, hδ₂_prop⟩ := hterm2 (ε/2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs hsd => ?_⟩
  have hp_s : IsProbabilityMeasure (f s) := (hf_mom s hs).1
  have hsd1 : dist s s₀ < δ₁ := lt_of_lt_of_le hsd (min_le_left _ _)
  have hsd2 : dist s s₀ < δ₂ := lt_of_lt_of_le hsd (min_le_right _ _)
  -- pointwise: |G s z - G s₀ z| ≤ ε/2 (uniform continuity on K; both zero off K)
  have hpoint : ∀ z, |G s z - G s₀ z| ≤ ε/2 := by
    intro z
    by_cases hzK : z ∈ K
    · have hp : ((s, z) : ℝ × PhaseSpace d) ∈ Set.Icc (0 : ℝ) T ×ˢ K := ⟨hs, hzK⟩
      have hq : ((s₀, z) : ℝ × PhaseSpace d) ∈ Set.Icc (0 : ℝ) T ×ˢ K := ⟨hs₀, hzK⟩
      have hdpq : dist ((s, z) : ℝ × PhaseSpace d) (s₀, z) < δ₁ := by
        rw [Prod.dist_eq]
        exact max_lt hsd1 (by rw [dist_self]; exact hδ₁)
      have hlt := hδ₁_prop _ hp _ hq hdpq
      rw [Real.dist_eq] at hlt
      exact le_of_lt hlt
    · rw [hG_supp s z hzK, hG_supp s₀ z hzK, sub_zero, abs_zero]; positivity
  -- split the s-integral
  have key : ∫ z, G s z ∂(f s) - ∫ z, G s₀ z ∂(f s)
      = ∫ z, (G s z - G s₀ z) ∂(f s) :=
    (integral_sub (hGint s s hs) (hGint s₀ s hs)).symm
  have hfirst : dist (∫ z, G s z ∂(f s)) (∫ z, G s₀ z ∂(f s)) ≤ ε/2 := by
    rw [Real.dist_eq, key]
    calc |∫ z, (G s z - G s₀ z) ∂(f s)|
        ≤ ∫ z, |G s z - G s₀ z| ∂(f s) := by
            have h := norm_integral_le_integral_norm (μ := f s) (fun z => G s z - G s₀ z)
            simpa only [Real.norm_eq_abs] using h
      _ ≤ ∫ _z, (ε/2) ∂(f s) :=
            integral_mono (((hGint s s hs).sub (hGint s₀ s hs)).abs)
              (integrable_const _) hpoint
      _ = ε/2 := by simp
  have hsecond : dist (∫ z, G s₀ z ∂(f s)) (∫ z, G s₀ z ∂(f s₀)) < ε/2 :=
    hδ₂_prop hs hsd2
  calc dist (∫ z, G s z ∂(f s)) (∫ z, G s₀ z ∂(f s₀))
      ≤ dist (∫ z, G s z ∂(f s)) (∫ z, G s₀ z ∂(f s))
        + dist (∫ z, G s₀ z ∂(f s)) (∫ z, G s₀ z ∂(f s₀)) := dist_triangle _ _ _
    _ < ε/2 + ε/2 := add_lt_add_of_le_of_lt hfirst hsecond
    _ = ε := by ring

end Vlasov

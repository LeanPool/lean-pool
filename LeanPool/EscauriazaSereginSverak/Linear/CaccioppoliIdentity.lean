/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivMollify
public import LeanPool.EscauriazaSereginSverak.Linear.CaccioppoliCutoff
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolev
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevSupport
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Local energy estimate for a parabolic differential inequality

This file proves the localized energy estimate in `lem:caccioppoli`.
-/

public section

open CKN CKN.Foundation.Parabolic Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

namespace ESS

private theorem inner_toLp_eq_integral_mul
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [Real.inner_apply]
  rw [hfx, hgx]

private theorem tendsto_integral_mul_spaceTimeMollify
    {f g b : Vec3 × ℝ → ℝ} (hf : MemLp f 2 (volume : Measure (Vec3 × ℝ)))
    (hg : MemLp g 2 (volume : Measure (Vec3 × ℝ)))
    (hb : AEStronglyMeasurable b (volume : Measure (Vec3 × ℝ)))
    {C : NNReal} (hC : ∀ q, ‖b q‖₊ ≤ C)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ n, 0 < δ n) :
    Tendsto
      (fun n => ∫ q, b q * spaceTimeMollify f (δ n) (hδpos n) q * g q
        ∂(volume : Measure (Vec3 × ℝ))) atTop
      (𝓝 (∫ q, b q * f q * g q ∂(volume : Measure (Vec3 × ℝ)))) := by
  let fn : ℕ → Vec3 × ℝ → ℝ := fun n => spaceTimeMollify f (δ n) (hδpos n)
  have hfn : ∀ n, MemLp (fn n) 2 (volume : Measure (Vec3 × ℝ)) := by
    intro n
    rw [memLp_iff]
    exact (spaceTimeMollify_eLpNorm_le (hδpos n) hf).trans_lt hf.eLpNorm_lt_top
  have hconv : Tendsto
      (fun n => eLpNorm (fn n - f) 2 (volume : Measure (Vec3 × ℝ))) atTop (𝓝 0) := by
    change Tendsto (fun n => eLpNorm
      (fun q => spaceTimeMollify f (δ n) (hδpos n) q - f q)
        2 (volume : Measure (Vec3 × ℝ))) atTop (𝓝 0)
    exact tendsto_eLpNorm_sub_zero_spaceTimeMollify hf hδ hδpos
  have hweighted := tendsto_toLp_mul_left_of_nnnorm_bound hb hC hfn hf hconv
  let hm (n : ℕ) : MemLp (fun q => b q * fn n q) 2
      (volume : Measure (Vec3 × ℝ)) := by
    apply (hfn n).of_nnnorm_le_mul (hb.mul (hfn n).aestronglyMeasurable)
    filter_upwards [] with q
    calc
      ‖b q * fn n q‖₊ = ‖b q‖₊ * ‖fn n q‖₊ := nnnorm_mul _ _
      _ ≤ C * ‖fn n q‖₊ :=
        mul_le_mul_of_nonneg_right (hC q) (by positivity)
  let hmLimit : MemLp (fun q => b q * f q) 2 (volume : Measure (Vec3 × ℝ)) := by
    apply hf.of_nnnorm_le_mul (hb.mul hf.aestronglyMeasurable)
    filter_upwards [] with q
    calc
      ‖b q * f q‖₊ = ‖b q‖₊ * ‖f q‖₊ := nnnorm_mul _ _
      _ ≤ C * ‖f q‖₊ := mul_le_mul_of_nonneg_right (hC q) (by positivity)
  have hpair : Tendsto
      (fun n => inner ℝ ((hm n).toLp (fun q => b q * fn n q)) (hg.toLp g)) atTop
      (𝓝 (inner ℝ (hmLimit.toLp (fun q => b q * f q)) (hg.toLp g))) :=
    Filter.Tendsto.inner hweighted
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => hg.toLp g) atTop (𝓝 (hg.toLp g)))
  have hseqEq (n : ℕ) :
      (∫ q, b q * fn n q * g q ∂(volume : Measure (Vec3 × ℝ))) =
        inner ℝ ((hm n).toLp (fun q => b q * fn n q)) (hg.toLp g) := by
    symm
    exact inner_toLp_eq_integral_mul (hm n) hg
  have hlimEq :
      (∫ q, b q * f q * g q ∂(volume : Measure (Vec3 × ℝ))) =
        inner ℝ (hmLimit.toLp (fun q => b q * f q)) (hg.toLp g) := by
    symm
    exact inner_toLp_eq_integral_mul hmLimit hg
  have hseq :
      (fun n => ∫ q, b q * fn n q * g q ∂(volume : Measure (Vec3 × ℝ))) =
        fun n => inner ℝ ((hm n).toLp (fun q => b q * fn n q)) (hg.toLp g) := by
    funext n
    exact hseqEq n
  rw [hseq, hlimEq]
  exact hpair

private theorem spaceTimeMollify_eq_of_closedBall
    {f g : Vec3 × ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) {z : Vec3 × ℝ}
    (hfg : ∀ q ∈ Metric.closedBall z δ, f q = g q) :
    spaceTimeMollify f δ hδ z = spaceTimeMollify g δ hδ z := by
  change (∫ q, spaceTimeMollifier δ hδ q * f (z - q)
      ∂(volume : Measure (Vec3 × ℝ))) =
    ∫ q, spaceTimeMollifier δ hδ q * g (z - q)
      ∂(volume : Measure (Vec3 × ℝ))
  apply integral_congr_ae
  have hkernel : tsupport (spaceTimeMollifier δ hδ) =
      Metric.closedBall (0 : Vec3 × ℝ) δ := by
    simpa [spaceTimeMollify, spaceTimeMollifier, spaceTimeStandardBump] using
      (spaceTimeStandardBump δ hδ).tsupport_normed_eq
  filter_upwards [] with q
  by_cases hzero : spaceTimeMollifier δ hδ q = 0
  · simp [hzero]
  · have hq : q ∈ tsupport (spaceTimeMollifier δ hδ) :=
      subset_tsupport _ (Function.mem_support.mpr hzero)
    rw [hkernel, Metric.mem_closedBall] at hq
    have hdist : dist (z - q) z = dist q 0 := by
      simpa only [sub_zero] using dist_sub_left z q 0
    have hmem : z - q ∈ Metric.closedBall z δ := by
      rw [Metric.mem_closedBall, hdist]
      exact hq
    rw [hfg (z - q) hmem]

private theorem zeroExtend_mollify_spatial_fderiv
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    {i j : Fin 3} {δ : ℝ} (hδ : 0 < δ) {q : Vec3 × ℝ}
    (hq : Metric.closedBall q (4 * δ) ⊆ Ω ×ˢ I) :
    fderiv ℝ (spaceTimeMollify
      (fun z : Vec3 × ℝ => ((Ω ×ˢ I).indicator
        (fun y => w (parabolicHomeomorph.symm y)) z) i) δ hδ) q (basisVec j, 0) =
      spaceTimeMollify
        (fun z : Vec3 × ℝ => ((Ω ×ˢ I).indicator
          (fun y => Dw (parabolicHomeomorph.symm y) i j) z)) δ hδ q := by
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let u : Vec3 × ℝ → ℝ := fun z => w (parabolicHomeomorph.symm z) i
  let g : Vec3 × ℝ → ℝ := fun z => Dw (parabolicHomeomorph.symm z) i j
  let uExt : Vec3 × ℝ → ℝ := fun z => (U.indicator u) z
  let gExt : Vec3 × ℝ → ℝ := fun z => (U.indicator g) z
  have hU : IsOpen U := by exact hΩ.prod hI
  have hK : Metric.closedBall q (3 * δ) ⊆ U := by
    intro z hz
    apply hq
    rw [Metric.mem_closedBall] at hz ⊢
    exact le_trans hz (by linarith only [hδ])
  have huProd : LocallyIntegrableOn
      (fun z : Vec3 × ℝ => w (parabolicHomeomorph.symm z)) U
      (volume : Measure (Vec3 × ℝ)) := by
    simpa [U] using locallyIntegrableOn_parabolic_to_product hΩ hI hderiv.1
  have hu : LocallyIntegrableOn u U (volume : Measure (Vec3 × ℝ)) := by
    intro z hz
    rcases huProd z hz with ⟨K, hzK, hKint⟩
    refine ⟨K, hzK, ?_⟩
    have hmeas : AEStronglyMeasurable (fun y => w (parabolicHomeomorph.symm y) i)
        (volume.restrict K) :=
      (continuous_apply i).comp_aestronglyMeasurable hKint.1
    have hbound : ∀ᵐ y ∂(volume.restrict K),
        ‖w (parabolicHomeomorph.symm y) i‖ ≤
          ‖‖w (parabolicHomeomorph.symm y)‖‖ := by
      filter_upwards [] with y
      simpa using norm_le_pi_norm (w (parabolicHomeomorph.symm y)) i
    exact hKint.norm.mono hmeas hbound
  have hDwProd : LocallyIntegrableOn
      (fun z : Vec3 × ℝ => Dw (parabolicHomeomorph.symm z)) U
      (volume : Measure (Vec3 × ℝ)) := by
    simpa [U] using locallyIntegrableOn_parabolic_to_product hΩ hI hderiv.2.1
  have hDwi : LocallyIntegrableOn
      (fun z : Vec3 × ℝ => Dw (parabolicHomeomorph.symm z) i) U
      (volume : Measure (Vec3 × ℝ)) := by
    intro z hz
    rcases hDwProd z hz with ⟨K, hzK, hKint⟩
    refine ⟨K, hzK, ?_⟩
    have hmeas : AEStronglyMeasurable
        (fun y => Dw (parabolicHomeomorph.symm y) i) (volume.restrict K) :=
      (continuous_apply i).comp_aestronglyMeasurable hKint.1
    have hbound : ∀ᵐ y ∂(volume.restrict K),
        ‖Dw (parabolicHomeomorph.symm y) i‖ ≤
          ‖‖Dw (parabolicHomeomorph.symm y)‖‖ := by
      filter_upwards [] with y
      simpa using norm_le_pi_norm (Dw (parabolicHomeomorph.symm y)) i
    exact hKint.norm.mono hmeas hbound
  have hg : LocallyIntegrableOn g U (volume : Measure (Vec3 × ℝ)) := by
    intro z hz
    rcases hDwi z hz with ⟨K, hzK, hKint⟩
    refine ⟨K, hzK, ?_⟩
    have hmeas : AEStronglyMeasurable
        (fun y => Dw (parabolicHomeomorph.symm y) i j) (volume.restrict K) :=
      (continuous_apply j).comp_aestronglyMeasurable hKint.1
    have hbound : ∀ᵐ y ∂(volume.restrict K),
        ‖Dw (parabolicHomeomorph.symm y) i j‖ ≤
          ‖‖Dw (parabolicHomeomorph.symm y) i‖‖ := by
      filter_upwards [] with y
      simpa using norm_le_pi_norm (Dw (parabolicHomeomorph.symm y) i) j
    exact hKint.norm.mono hmeas hbound
  have hweak : ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Metric.closedBall q (3 * δ) →
      (∫ z in U, u z * (fderiv ℝ φ z) (basisVec j, 0)
          ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ z in U, g z * φ z ∂(volume : Measure (Vec3 × ℝ)) := by
    intro φ hφ hφc hφK
    simpa [u, g, U] using
      weak_spatial_identity_product hΩ hI hderiv hφ hφc (hφK.trans hK) i j
  have hraw := spaceTimeMollify_fderiv_eq_of_local_weak
    hU hu hg hδ hK hweak
  have hlocalEq : spaceTimeMollify u δ hδ =ᶠ[𝓝 q]
      spaceTimeMollify uExt δ hδ := by
    filter_upwards [Metric.ball_mem_nhds q hδ] with z hz
    symm
    apply spaceTimeMollify_eq_of_closedBall hδ
    intro y hy
    have hyq : y ∈ Metric.closedBall q (2 * δ) := by
      rw [Metric.mem_closedBall] at hy ⊢
      have hdist : dist y q ≤ dist y z + dist z q := dist_triangle _ _ _
      have hy' : dist y z ≤ δ := Metric.mem_closedBall.mp hy
      have hz' : dist z q < δ := Metric.mem_ball.mp hz
      have hsum : dist y z + dist z q ≤ δ + δ :=
        add_le_add hy' hz'.le
      calc
        dist y q ≤ dist y z + dist z q := hdist
        _ ≤ δ + δ := hsum
        _ = 2 * δ := by ring
    have hyU : y ∈ U := by
      apply hq
      rw [Metric.mem_closedBall] at hyq ⊢
      exact le_trans hyq (by linarith only [hδ])
    simp [uExt, Set.indicator, U, hyU]
  have hrawHas := hraw.1.congr_of_eventuallyEq hlocalEq.symm
  have hleft :
      fderiv ℝ (spaceTimeMollify uExt δ hδ) q (basisVec j, 0) =
        fderiv ℝ (spaceTimeMollify u δ hδ) q (basisVec j, 0) := by
    exact congrArg (fun L : (Vec3 × ℝ) →L[ℝ] ℝ => L (basisVec j, 0))
      hrawHas.fderiv
  have hright : spaceTimeMollify g δ hδ q = spaceTimeMollify gExt δ hδ q := by
    apply spaceTimeMollify_eq_of_closedBall hδ
    intro y hy
    have hyU : y ∈ U := by
      apply hq
      rw [Metric.mem_closedBall] at hy ⊢
      exact le_trans hy (by linarith only [hδ])
    simp [gExt, Set.indicator, U, hyU]
  have huExtEq :
      (fun z : Vec3 × ℝ => ((Ω ×ˢ I).indicator
        (fun y => w (parabolicHomeomorph.symm y)) z) i) = uExt := by
    funext z
    by_cases hz : z ∈ U <;> simp [uExt, u, U, hz]
  have hDwExtEq :
      (fun z : Vec3 × ℝ => ((Ω ×ˢ I).indicator
        (fun y => Dw (parabolicHomeomorph.symm y) i j) z)) = gExt := by
    funext z
    by_cases hz : z ∈ U <;> simp [gExt, g, U, hz]
  rw [huExtEq, hDwExtEq]
  exact hleft.trans (hraw.2.trans hright)

private theorem localized_spatial_energy_component
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hbuffer : ∀ q ∈ tsupport φ,
      Metric.closedBall q (4 * δ₀) ⊆ Ω ×ˢ I)
    (i j : Fin 3) :
    (∫ q : Vec3 × ℝ,
      φ q * (((Ω ×ˢ I).indicator
        (fun y => w (parabolicHomeomorph.symm y)) q) i) *
        (((Ω ×ˢ I).indicator
          (fun y => D2w (parabolicHomeomorph.symm y)) q) i j j)
        ∂(volume : Measure (Vec3 × ℝ))) =
      -(∫ q : Vec3 × ℝ,
        φ q * ((((Ω ×ˢ I).indicator
          (fun y => Dw (parabolicHomeomorph.symm y)) q) i j) ^ 2)
        ∂(volume : Measure (Vec3 × ℝ))) -
      ∫ q : Vec3 × ℝ,
        (fderiv ℝ φ q) (basisVec j, 0) *
          (((Ω ×ˢ I).indicator
            (fun y => w (parabolicHomeomorph.symm y)) q) i) *
          (((Ω ×ˢ I).indicator
            (fun y => Dw (parabolicHomeomorph.symm y)) q) i j)
        ∂(volume : Measure (Vec3 × ℝ)) := by
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let u : Vec3 × ℝ → ℝ := fun q => (U.indicator
    (fun y => w (parabolicHomeomorph.symm y)) q) i
  let g : Vec3 × ℝ → ℝ := fun q => (U.indicator
    (fun y => Dw (parabolicHomeomorph.symm y)) q) i j
  let h : Vec3 × ℝ → ℝ := fun q => (U.indicator
    (fun y => D2w (parabolicHomeomorph.symm y)) q) i j j
  have hUopen : IsOpen U := hΩ.prod hI
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hdata := zeroExtend_spaceTimeData_memLp hΩ hI hderiv hL2
  have hu : MemLp u 2 (volume : Measure (Vec3 × ℝ)) := by
    change MemLp (fun q : Vec3 × ℝ =>
      ((U.indicator (fun y => w (parabolicHomeomorph.symm y)) q) i)) 2 _
    simpa [zeroExtendField, U, Set.indicator] using memLp_pi_component hdata.1 i
  have hg : MemLp g 2 (volume : Measure (Vec3 × ℝ)) := by
    change MemLp (fun q : Vec3 × ℝ =>
      ((U.indicator (fun y => Dw (parabolicHomeomorph.symm y)) q) i j)) 2 _
    simpa [zeroExtendField, U, Set.indicator] using
      memLp_pi_component (memLp_pi_component hdata.2.1 i) j
  have hh : MemLp h 2 (volume : Measure (Vec3 × ℝ)) := by
    change MemLp (fun q : Vec3 × ℝ =>
      ((U.indicator (fun y => D2w (parabolicHomeomorph.symm y)) q) i j j)) 2 _
    simpa [zeroExtendField, U, Set.indicator] using
      memLp_pi_component (memLp_pi_component
        (memLp_pi_component hdata.2.2.1 i) j) j
  let δ : ℕ → ℝ := fun n => δ₀ / (n + 1 : ℝ)
  have hδpos (n : ℕ) : 0 < δ n := by
    apply div_pos hδ₀
    positivity
  have hδle (n : ℕ) : δ n ≤ δ₀ := by
    apply div_le_self hδ₀.le
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith only [hn]
  have hδtendsto : Tendsto δ atTop (𝓝 0) := by
    simpa [δ, div_eq_mul_inv] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  let un (n : ℕ) : Vec3 × ℝ → ℝ := spaceTimeMollify u (δ n) (hδpos n)
  let gn (n : ℕ) : Vec3 × ℝ → ℝ := spaceTimeMollify g (δ n) (hδpos n)
  have hunSmooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (un n) := by
    apply spaceTimeMollify_contDiff (hδpos n)
    exact hu.locallyIntegrable (by norm_num)
  have hgnSmooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (gn n) := by
    apply spaceTimeMollify_contDiff (hδpos n)
    exact hg.locallyIntegrable (by norm_num)
  have hunMem (n : ℕ) : MemLp (un n) 2 (volume : Measure (Vec3 × ℝ)) := by
    exact (spaceTimeMollify_eLpNorm_le (hδpos n) hu).trans_lt hu.eLpNorm_lt_top
  have hgnMem (n : ℕ) : MemLp (gn n) 2 (volume : Measure (Vec3 × ℝ)) := by
    exact (spaceTimeMollify_eLpNorm_le (hδpos n) hg).trans_lt hg.eLpNorm_lt_top
  have hφbound : ∃ C : NNReal, ∀ q, ‖φ q‖₊ ≤ C :=
    continuous_hasCompactSupport_nnnorm_bound hφ.continuous hφc
  let b : Vec3 × ℝ → ℝ := fun q => (fderiv ℝ φ q) (basisVec j, 0)
  have hbcont : Continuous b := by
    dsimp [b]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hbc : HasCompactSupport b := by
    dsimp [b]
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec j, 0)
  obtain ⟨Cb, hCb⟩ := continuous_hasCompactSupport_nnnorm_bound hbcont hbc
  have hbmeas : AEStronglyMeasurable b (volume : Measure (Vec3 × ℝ)) :=
    hbcont.aestronglyMeasurable
  have hφmeas : AEStronglyMeasurable φ (volume : Measure (Vec3 × ℝ)) :=
    hφ.continuous.aestronglyMeasurable
  rcases hφbound with ⟨Cφ, hCφ⟩
  let χ (n : ℕ) : Vec3 × ℝ → ℝ := fun q => φ q * un n q
  have hχsmooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (χ n) :=
    hφ.mul (hunSmooth n)
  have hχcompact (n : ℕ) : HasCompactSupport (χ n) := hφc.mul_right
  have hbuffer_subset : tsupport φ ⊆ Ω ×ˢ I := by
    intro q hq
    have hcenter : q ∈ Metric.closedBall q (4 * δ₀) := by
      rw [Metric.mem_closedBall]
      simp [hδ₀.le]
    exact hbuffer q hq hcenter
  have hχsupport (n : ℕ) : tsupport (χ n) ⊆ U := by
    exact (tsupport_mul_subset_left).trans (by simpa [U] using hbuffer_subset)
  have hweak : ∀ n : ℕ,
      (∫ q in U, Dw (parabolicHomeomorph.symm q) i j *
        (fderiv ℝ (χ n) q) (basisVec j, 0)
        ∂(volume : Measure (Vec3 × ℝ))) =
      -∫ q in U, D2w (parabolicHomeomorph.symm q) i j j * χ n q
        ∂(volume : Measure (Vec3 × ℝ)) := by
    intro n
    exact weak_spatialSecond_identity_product hΩ hI hderiv
      (hχsmooth n) (hχcompact n) (hχsupport n) i j j
  have hglobal (n : ℕ) :
      (∫ q, g q * (fderiv ℝ (χ n) q) (basisVec j, 0)
        ∂(volume : Measure (Vec3 × ℝ))) =
      -∫ q, h q * χ n q ∂(volume : Measure (Vec3 × ℝ)) := by
    have hleft :
        (∫ q, g q * (fderiv ℝ (χ n) q) (basisVec j, 0)
          ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ q in U, Dw (parabolicHomeomorph.symm q) i j *
          (fderiv ℝ (χ n) q) (basisVec j, 0)
          ∂(volume : Measure (Vec3 × ℝ)) := by
      have hfun : (fun q => g q * (fderiv ℝ (χ n) q) (basisVec j, 0)) =
          U.indicator (fun q => Dw (parabolicHomeomorph.symm q) i j *
            (fderiv ℝ (χ n) q) (basisVec j, 0)) := by
        funext q
        by_cases hq : q ∈ U
        · simp [g, hq]
        · have hnot : q ∉ tsupport (χ n) := fun hmem => hq (hχsupport n hmem)
          have hfd : fderiv ℝ (χ n) q = 0 := fderiv_of_notMem_tsupport ℝ hnot
          simp [g, Set.indicator, hq, hfd]
      rw [hfun, integral_indicator hUmeas]
    have hright :
        (∫ q, h q * χ n q ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ q in U, D2w (parabolicHomeomorph.symm q) i j j * χ n q
          ∂(volume : Measure (Vec3 × ℝ)) := by
      have hfun : (fun q => h q * χ n q) =
          U.indicator (fun q => D2w (parabolicHomeomorph.symm q) i j j * χ n q) := by
        funext q
        by_cases hq : q ∈ U <;> simp [h, Set.indicator, χ, hq]
      rw [hfun, integral_indicator hUmeas]
    rw [hleft, hright]
    exact hweak n
  have hderivative (n : ℕ) (q : Vec3 × ℝ) :
      (fderiv ℝ (χ n) q) (basisVec j, 0) =
        b q * un n q + φ q * (fderiv ℝ (un n) q) (basisVec j, 0) := by
    have hmul := fderiv_mul
      (hφ.differentiable (by simp) q) ((hunSmooth n).differentiable (by simp) q)
    change (fderiv ℝ (φ * un n) q) (basisVec j, 0) = _
    rw [hmul]
    simp [smul_eq_mul, b, mul_comm]
    ring
  have hlocalderivative (n : ℕ) (q : Vec3 × ℝ) (hq : q ∈ tsupport φ) :
      (fderiv ℝ (un n) q) (basisVec j, 0) = gn n q := by
    have hball : Metric.closedBall q (4 * δ n) ⊆ U := by
      exact (Metric.closedBall_subset_closedBall (by nlinarith only [hδle n])).trans
        (hbuffer q hq)
    have hraw := zeroExtend_mollify_spatial_fderiv hΩ hI hderiv
      (i := i) (j := j) (δ := δ n) (hδpos n) (q := q) hball
    have hgIdent : g = (fun z => U.indicator
        (fun y => Dw (parabolicHomeomorph.symm y) i j) z) := by
      funext z
      by_cases hz : z ∈ U <;> simp [g, Set.indicator, hz]
    change (fderiv ℝ (spaceTimeMollify u (δ n) (hδpos n)) q) (basisVec j, 0) =
      spaceTimeMollify g (δ n) (hδpos n) q
    rw [hgIdent]
    change (fderiv ℝ (spaceTimeMollify
        (fun z => (U.indicator (fun y => w (parabolicHomeomorph.symm y)) z) i)
        (δ n) (hδpos n)) q) (basisVec j, 0) =
      spaceTimeMollify
        (fun z => U.indicator
        (fun y => Dw (parabolicHomeomorph.symm y) i j) z) (δ n) (hδpos n) q
    simpa [U] using hraw
  let A (n : ℕ) : ℝ := ∫ q, b q * un n q * g q
    ∂(volume : Measure (Vec3 × ℝ))
  let B (n : ℕ) : ℝ := ∫ q, φ q * gn n q * g q
    ∂(volume : Measure (Vec3 × ℝ))
  let C (n : ℕ) : ℝ := ∫ q, φ q * un n q * h q
    ∂(volume : Measure (Vec3 × ℝ))
  have hAintegrable (n : ℕ) : Integrable (fun q => b q * un n q * g q)
      (volume : Measure (Vec3 × ℝ)) := by
    have hbun : MemLp (fun q => b q * un n q) 2
        (volume : Measure (Vec3 × ℝ)) :=
      memLp_mul_left_of_nnnorm_bound hbmeas (hunMem n) (ae_of_all _ hCb)
    exact hbun.integrable_mul hg
  have hBintegrable (n : ℕ) : Integrable (fun q => φ q * gn n q * g q)
      (volume : Measure (Vec3 × ℝ)) := by
    have hφgn : MemLp (fun q => φ q * gn n q) 2
        (volume : Measure (Vec3 × ℝ)) :=
      memLp_mul_left_of_nnnorm_bound hφmeas (hgnMem n) (ae_of_all _ hCφ)
    exact hφgn.integrable_mul hg
  have hCintegrable (n : ℕ) : Integrable (fun q => φ q * un n q * h q)
      (volume : Measure (Vec3 × ℝ)) := by
    have hφun : MemLp (fun q => φ q * un n q) 2
        (volume : Measure (Vec3 × ℝ)) :=
      memLp_mul_left_of_nnnorm_bound hφmeas (hunMem n) (ae_of_all _ hCφ)
    exact hφun.integrable_mul hh
  have hseq (n : ℕ) : C n = -B n - A n := by
    have hsum :
        (∫ q, g q * (fderiv ℝ (χ n) q) (basisVec j, 0)
          ∂(volume : Measure (Vec3 × ℝ))) =
        A n + B n := by
      calc
        _ = ∫ q, (b q * un n q * g q) +
              (φ q * gn n q * g q) ∂(volume : Measure (Vec3 × ℝ)) := by
          apply integral_congr_ae
          filter_upwards [] with q
          by_cases hq : q ∈ tsupport φ
          · rw [hderivative n q, hlocalderivative n q hq]
            dsimp [g]
            ring
          · have hφzero : φ q = 0 := image_eq_zero_of_notMem_tsupport hq
            have hbzero : b q = 0 := by
              have hfd : fderiv ℝ φ q = 0 := fderiv_of_notMem_tsupport ℝ hq
              simp [b, hfd]
            have hχzero : (fderiv ℝ (χ n) q) (basisVec j, 0) = 0 := by
              have hnot : q ∉ tsupport (χ n) := fun hm => hq (tsupport_mul_subset_left hm)
              rw [fderiv_of_notMem_tsupport ℝ hnot]
              simp
            rw [hχzero, hφzero, hbzero]
            simp
        _ = A n + B n := by
          rw [integral_add (hAintegrable n) (hBintegrable n)]
    have hrewrite :
      (∫ q, g q * (fderiv ℝ (χ n) q) (basisVec j, 0)
          ∂(volume : Measure (Vec3 × ℝ))) = -C n := by
      rw [hglobal n]
      dsimp [C, χ]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with q
      ring
    dsimp [A, B, C]
    rw [hsum] at hrewrite
    linarith only [hrewrite]
  have hAtendsto : Tendsto A atTop (𝓝
      (∫ q, b q * u q * g q ∂(volume : Measure (Vec3 × ℝ)))) := by
    change Tendsto (fun n => ∫ q, b q * spaceTimeMollify u (δ n) (hδpos n) q * g q
      ∂(volume : Measure (Vec3 × ℝ))) atTop _
    exact tendsto_integral_mul_spaceTimeMollify hu hg hbmeas (fun q => hCb q)
      hδtendsto hδpos
  have hBtendsto : Tendsto B atTop (𝓝
      (∫ q, φ q * g q * g q ∂(volume : Measure (Vec3 × ℝ)))) := by
    change Tendsto (fun n => ∫ q, φ q * spaceTimeMollify g (δ n) (hδpos n) q * g q
      ∂(volume : Measure (Vec3 × ℝ))) atTop _
    exact tendsto_integral_mul_spaceTimeMollify hg hg hφmeas (fun q => hCφ q)
      hδtendsto hδpos
  have hCtendsto : Tendsto C atTop (𝓝
      (∫ q, φ q * u q * h q ∂(volume : Measure (Vec3 × ℝ)))) := by
    change Tendsto (fun n => ∫ q, φ q * spaceTimeMollify u (δ n) (hδpos n) q * h q
      ∂(volume : Measure (Vec3 × ℝ))) atTop _
    exact tendsto_integral_mul_spaceTimeMollify hu hh hφmeas (fun q => hCφ q)
      hδtendsto hδpos
  have hrightlim : Tendsto (fun n => -B n - A n) atTop
      (𝓝 (-(∫ q, φ q * g q * g q ∂(volume : Measure (Vec3 × ℝ))) -
        ∫ q, b q * u q * g q ∂(volume : Measure (Vec3 × ℝ)))) :=
    hBtendsto.neg.sub hAtendsto
  have hCseq : C = fun n => -B n - A n := by
    funext n
    exact hseq n
  rw [hCseq] at hCtendsto
  have hlimit := tendsto_nhds_unique hCtendsto hrightlim
  simpa [u, g, h, b, U, pow_two, mul_assoc, mul_left_comm, mul_comm] using hlimit

/-- The local energy identity for a smooth compactly supported weight (`lem:caccioppoli`). -/
theorem localizedEnergyIdentity
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hbuffer : ∀ q ∈ tsupport φ,
      Metric.closedBall q (4 * δ₀) ⊆ Ω ×ˢ I) :
    (∑ i : Fin 3,
      ∫ q : Vec3 × ℝ,
        (((Ω ×ˢ I).indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) *
        (((Ω ×ˢ I).indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q) i) * φ q
        ∂(volume : Measure (Vec3 × ℝ))) +
    (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ q : Vec3 × ℝ,
        φ q * (((Ω ×ˢ I).indicator
          (fun y => w (parabolicHomeomorph.symm y)) q) i) *
          (((Ω ×ˢ I).indicator
            (fun y => D2w (parabolicHomeomorph.symm y)) q) i j j)
        ∂(volume : Measure (Vec3 × ℝ))) =
    -(1 / 2) * (∑ i : Fin 3,
      ∫ q : Vec3 × ℝ,
        (((Ω ×ˢ I).indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) ^ 2 *
          (fderiv ℝ φ q) (0, 1) ∂(volume : Measure (Vec3 × ℝ))) -
    (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ q : Vec3 × ℝ,
        φ q * ((((Ω ×ˢ I).indicator
          (fun y => Dw (parabolicHomeomorph.symm y)) q) i j) ^ 2)
        ∂(volume : Measure (Vec3 × ℝ))) -
    (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ q : Vec3 × ℝ,
        (fderiv ℝ φ q) (basisVec j, 0) *
          (((Ω ×ˢ I).indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) *
          (((Ω ×ˢ I).indicator (fun y => Dw (parabolicHomeomorph.symm y)) q) i j)
        ∂(volume : Measure (Vec3 × ℝ))) := by
  have hdata := zeroExtend_spaceTimeData_memLp hΩ hI hderiv hL2
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  have hWcoord (i : Fin 3) :
      (fun q : Vec3 × ℝ => ((spaceTimeSet Ω I).indicator w
        (parabolicHomeomorph.symm q)) i) =
      (fun q => ((U.indicator (fun y => w (parabolicHomeomorph.symm y)) q) i)) := by
    funext q
    rcases q with ⟨y, s⟩
    rfl
  have hTcoord (i : Fin 3) :
      (fun q : Vec3 × ℝ => ((spaceTimeSet Ω I).indicator Dtw
        (parabolicHomeomorph.symm q)) i) =
      (fun q => ((U.indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q) i)) := by
    funext q
    rcases q with ⟨y, s⟩
    rfl
  have hL2w (i : Fin 3) : MemLp
      (fun q : Vec3 × ℝ => ((spaceTimeSet Ω I).indicator w
        (parabolicHomeomorph.symm q)) i) 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hWcoord i]
    have hcomp : MemLp
        (fun q : Vec3 × ℝ => (U.indicator
          (fun y => w (parabolicHomeomorph.symm y)) q) i) 2
        (volume : Measure (Vec3 × ℝ)) := by
      simpa [zeroExtendField, U, Set.indicator,
        parabolicHomeomorph_symm_apply] using memLp_pi_component hdata.1 i
    exact hcomp
  have hL2time (i : Fin 3) : MemLp
      (fun q : Vec3 × ℝ => ((spaceTimeSet Ω I).indicator Dtw
        (parabolicHomeomorph.symm q)) i) 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hTcoord i]
    have hcomp : MemLp
        (fun q : Vec3 × ℝ => (U.indicator
          (fun y => Dtw (parabolicHomeomorph.symm y)) q) i) 2
        (volume : Measure (Vec3 × ℝ)) := by
      simpa [zeroExtendField, U, Set.indicator,
        parabolicHomeomorph_symm_apply] using memLp_pi_component hdata.2.2.2 i
    exact hcomp
  have htime := weak_time_derivative_sq hΩ hI hderiv hL2w hL2time
    hφ hφc hδ₀ hbuffer
  have hspace (i j : Fin 3) := localized_spatial_energy_component
    hΩ hI hderiv hL2 hφ hφc hδ₀ hbuffer i j
  have hspaceAll :
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ,
          φ q * (((Ω ×ˢ I).indicator
            (fun y => w (parabolicHomeomorph.symm y)) q) i) *
            (((Ω ×ˢ I).indicator
              (fun y => D2w (parabolicHomeomorph.symm y)) q) i j j)
          ∂(volume : Measure (Vec3 × ℝ))) =
      -(∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ,
          φ q * ((((Ω ×ˢ I).indicator
            (fun y => Dw (parabolicHomeomorph.symm y)) q) i j) ^ 2)
          ∂(volume : Measure (Vec3 × ℝ))) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ,
          (fderiv ℝ φ q) (basisVec j, 0) *
            (((Ω ×ˢ I).indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) *
            (((Ω ×ˢ I).indicator (fun y => Dw (parabolicHomeomorph.symm y)) q) i j)
          ∂(volume : Measure (Vec3 × ℝ))) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          (-(∫ q : Vec3 × ℝ,
            φ q * ((((Ω ×ˢ I).indicator
              (fun y => Dw (parabolicHomeomorph.symm y)) q) i j) ^ 2)
            ∂(volume : Measure (Vec3 × ℝ))) -
          ∫ q : Vec3 × ℝ,
            (fderiv ℝ φ q) (basisVec j, 0) *
              (((Ω ×ˢ I).indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) *
              (((Ω ×ˢ I).indicator (fun y => Dw (parabolicHomeomorph.symm y)) q) i j)
            ∂(volume : Measure (Vec3 × ℝ))) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hspace i j
      _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have htime' :
      (∑ i : Fin 3,
        ∫ q : Vec3 × ℝ,
          (((Ω ×ˢ I).indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) *
            (((Ω ×ˢ I).indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q) i) * φ q
          ∂(volume : Measure (Vec3 × ℝ))) =
      -(1 / 2) * (∑ i : Fin 3,
        ∫ q : Vec3 × ℝ,
          (((Ω ×ˢ I).indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) ^ 2 *
            (fderiv ℝ φ q) (0, 1) ∂(volume : Measure (Vec3 × ℝ))) := by
    have htimeProduct :
        (∑ i : Fin 3,
          ∫ q : Vec3 × ℝ,
            (((Ω ×ˢ I).indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) ^ 2 *
              (fderiv ℝ φ q) (0, 1) ∂(volume : Measure (Vec3 × ℝ))) =
        -(2 * (∑ i : Fin 3,
          ∫ q : Vec3 × ℝ,
            (((Ω ×ˢ I).indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) *
              (((Ω ×ˢ I).indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q) i) * φ q
              ∂(volume : Measure (Vec3 × ℝ)))) := by
      have htimeLhs :
          (∑ i : Fin 3,
            ∫ q : Vec3 × ℝ,
              (((U.indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) ^ 2) *
                (fderiv ℝ φ q) (0, 1) ∂(volume : Measure (Vec3 × ℝ))) =
          ∑ i : Fin 3,
            ∫ q : Vec3 × ℝ,
              (((spaceTimeSet Ω I).indicator w (parabolicHomeomorph.symm q) i) ^ 2) *
                (fderiv ℝ φ q) (0, 1) ∂(volume : Measure (Vec3 × ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
      have htimeRhs :
          (∑ i : Fin 3,
            ∫ q : Vec3 × ℝ,
              (((spaceTimeSet Ω I).indicator w (parabolicHomeomorph.symm q) i) *
                ((spaceTimeSet Ω I).indicator Dtw (parabolicHomeomorph.symm q) i) * φ q)
              ∂(volume : Measure (Vec3 × ℝ))) =
          ∑ i : Fin 3,
            ∫ q : Vec3 × ℝ,
              ((U.indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) *
                ((U.indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q) i) * φ q
              ∂(volume : Measure (Vec3 × ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
      calc
        _ = ∑ i : Fin 3,
            ∫ q : Vec3 × ℝ,
              (((spaceTimeSet Ω I).indicator w (parabolicHomeomorph.symm q) i) ^ 2) *
                (fderiv ℝ φ q) (0, 1) ∂(volume : Measure (Vec3 × ℝ)) := htimeLhs
        _ = -(2 * (∑ i : Fin 3,
            ∫ q : Vec3 × ℝ,
              (((spaceTimeSet Ω I).indicator w (parabolicHomeomorph.symm q) i) *
                ((spaceTimeSet Ω I).indicator Dtw (parabolicHomeomorph.symm q) i) * φ q)
              ∂(volume : Measure (Vec3 × ℝ)))) := htime
        _ = _ := by rw [htimeRhs]
    change (∑ i : Fin 3,
        ∫ q : Vec3 × ℝ,
          (((U.indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) *
            ((U.indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q) i) * φ q)
          ∂(volume : Measure (Vec3 × ℝ))) =
      -(1 / 2) * (∑ i : Fin 3,
        ∫ q : Vec3 × ℝ,
          (((U.indicator (fun y => w (parabolicHomeomorph.symm y)) q) i) ^ 2) *
            (fderiv ℝ φ q) (0, 1) ∂(volume : Measure (Vec3 × ℝ)))
    rw [htimeProduct]
    ring
  linarith only [hspaceAll, htime']

end ESS

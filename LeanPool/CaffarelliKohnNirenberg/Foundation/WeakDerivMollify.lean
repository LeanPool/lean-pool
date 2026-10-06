/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.FactorDerivative
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.FactorIBP
public import LeanPool.CaffarelliKohnNirenberg.Foundation.SpaceTimeMollifier
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weak derivatives and space-time mollification

The distributional identities in `def:sws` commute with local space-time
mollification on compact subsets of the domain.
-/

public section

open Filter Function MeasureTheory Set
open scoped Convolution Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private def piEvalCLM {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (i : ι) : (ι → E) →L[ℝ] E :=
  ContinuousLinearMap.mk (LinearMap.proj i) (by
    have hL : LipschitzWith 1 (fun x : ι → E => x i) := by
      intro x y
      have hdist : dist (x i) (y i) ≤ dist x y := by
        calc
          dist (x i) (y i) = ‖(x - y) i‖ := by simp [dist_eq_norm]
          _ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i
          _ = dist x y := by rw [dist_eq_norm]
      simpa [edist_dist] using hdist
    exact hL.continuous)

local instance :
    Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

/-- A scalar weak derivative commutes with space-time mollification in the interior
of the testing domain (manuscript `def:sws`). -/
private theorem spaceTimeMollify_fderiv_eq_of_global_weak
    {U : Set (Vec3 × ℝ)} {u g : Vec3 × ℝ → ℝ} {v : Vec3 × ℝ}
    (hweak : ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ y, u y * (fderiv ℝ φ y) v ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ y, g y * φ y ∂(volume : Measure (Vec3 × ℝ)))
    (hu : LocallyIntegrable u (volume : Measure (Vec3 × ℝ)))
    {δ : ℝ} (hδ : 0 < δ) {z : Vec3 × ℝ}
    (hz : Metric.closedBall z δ ⊆ U) :
    (fderiv ℝ (spaceTimeMollify u δ hδ) z) v =
      spaceTimeMollify g δ hδ z := by
  let k : Vec3 × ℝ → ℝ := spaceTimeMollifier δ hδ
  let φ : Vec3 × ℝ → ℝ := fun y => k (z - y)
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := spaceTimeMollifier_contDiff hδ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    exact hk.comp (contDiff_const.sub contDiff_id)
  have hφSupport : HasCompactSupport φ := by
    simpa [φ, Function.comp_def] using
      (spaceTimeMollifier_hasCompactSupport hδ).comp_homeomorph (Homeomorph.subLeft z)
  have hφSubset : tsupport φ ⊆ U := by
    have hts : tsupport φ = (Homeomorph.subLeft z) ⁻¹' tsupport k := by
      simpa [φ, Function.comp_def] using tsupport_comp_eq_preimage k (Homeomorph.subLeft z)
    have hkt : tsupport k = Metric.closedBall (0 : Vec3 × ℝ) δ := by
      simpa [k, spaceTimeMollifier, spaceTimeStandardBump] using
        (spaceTimeStandardBump δ hδ).tsupport_normed_eq
    rw [hts, hkt]
    intro y hy
    change z - y ∈ Metric.closedBall (0 : Vec3 × ℝ) δ at hy
    apply hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa [norm_sub_rev] using hy
  have hfd := (spaceTimeMollifier_hasCompactSupport hδ).hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (spaceTimeMollifier_contDiff hδ (n := 1)) hu z
  have hfd' : fderiv ℝ (spaceTimeMollify u δ hδ) z =
      (MeasureTheory.convolution (fderiv ℝ (spaceTimeMollifier δ hδ)) u
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec3 × ℝ))
        (volume : Measure (Vec3 × ℝ))) z := by
    simpa [spaceTimeMollify] using hfd.fderiv
  rw [hfd']
  simp only [MeasureTheory.convolution, ContinuousLinearMap.lsmul_apply, spaceTimeMollify]
  have hKderiv : HasCompactSupport (fun t : Vec3 × ℝ =>
      fderiv ℝ (spaceTimeMollifier δ hδ) t) :=
    (spaceTimeMollifier_hasCompactSupport hδ).fderiv (𝕜 := ℝ)
  have hderivCont : Continuous (fun t : Vec3 × ℝ =>
      fderiv ℝ (spaceTimeMollifier δ hδ) t) :=
    (spaceTimeMollifier_contDiff hδ (n := 2)).continuous_fderiv (by simp)
  have hconv : ConvolutionExists (fderiv ℝ (spaceTimeMollifier δ hδ)) u
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec3 × ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    exact HasCompactSupport.convolutionExists_left
      (𝕜 := ℝ) (G := Vec3 × ℝ) (E := (Vec3 × ℝ) →L[ℝ] ℝ)
      (E' := ℝ) (F := (Vec3 × ℝ) →L[ℝ] ℝ)
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec3 × ℝ))
      hKderiv hderivCont hu
  rw [ContinuousLinearMap.integral_apply (hconv z) v]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]
  change (∫ t, (fderiv ℝ (spaceTimeMollifier δ hδ) t) v * u (z - t)
      ∂(volume : Measure (Vec3 × ℝ))) =
    ∫ t, spaceTimeMollifier δ hδ t * g (z - t) ∂(volume : Measure (Vec3 × ℝ))
  have hφDeriv (y : Vec3 × ℝ) :
      (fderiv ℝ φ y) v = - (fderiv ℝ k (z - y)) v := by
    have hinner : HasFDerivAt (fun q : Vec3 × ℝ => z - q)
        (-(1 : Vec3 × ℝ →L[ℝ] Vec3 × ℝ)) y :=
      (hasFDerivAt_id y).const_sub z
    have houter : HasFDerivAt k (fderiv ℝ k (z - y)) (z - y) :=
      (hk.differentiable (by simp) (z - y)).hasFDerivAt
    have hcomp := houter.comp y hinner
    simpa [φ, Function.comp_def, ContinuousLinearMap.comp_apply] using
      congrArg (fun L : (Vec3 × ℝ) →L[ℝ] ℝ => L v) hcomp.fderiv
  have hweakGlobal :
      (∫ y, u y * (fderiv ℝ φ y) v ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ y, g y * φ y ∂(volume : Measure (Vec3 × ℝ)) :=
    hweak φ hφ hφSupport hφSubset
  have hchange :
      (∫ t, (fderiv ℝ (spaceTimeMollifier δ hδ) t) v * u (z - t)
          ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ y, u y * (fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)) v
          ∂(volume : Measure (Vec3 × ℝ)) := by
    calc
      (∫ t, (fderiv ℝ (spaceTimeMollifier δ hδ) t) v * u (z - t)
          ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ t, u (z - t) * (fderiv ℝ (spaceTimeMollifier δ hδ) t) v
            ∂(volume : Measure (Vec3 × ℝ)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        ring
      _ = ∫ y, u y * (fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)) v
          ∂(volume : Measure (Vec3 × ℝ)) := by
        let F : Vec3 × ℝ → ℝ := fun y =>
          u y * (fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)) v
        simpa [F, sub_sub_cancel] using
          (Measure.measurePreserving_sub_left (volume : Measure (Vec3 × ℝ)) z).integral_comp
            (Homeomorph.subLeft z).measurableEmbedding F
  have hright :
      (∫ t, spaceTimeMollifier δ hδ t * g (z - t)
          ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ y, g y * φ y ∂(volume : Measure (Vec3 × ℝ)) := by
    let F : Vec3 × ℝ → ℝ := fun y => φ y * g y
    calc
      (∫ t, spaceTimeMollifier δ hδ t * g (z - t)
          ∂(volume : Measure (Vec3 × ℝ))) = ∫ t, F (z - t)
            ∂(volume : Measure (Vec3 × ℝ)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        simp [F, φ, k]
      _ = ∫ y, F y ∂(volume : Measure (Vec3 × ℝ)) :=
        (Measure.measurePreserving_sub_left (volume : Measure (Vec3 × ℝ)) z).integral_comp
          (Homeomorph.subLeft z).measurableEmbedding F
      _ = ∫ y, g y * φ y ∂(volume : Measure (Vec3 × ℝ)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp [F, mul_comm]
  calc
    (∫ t, (fderiv ℝ (spaceTimeMollifier δ hδ) t) v * u (z - t)
        ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ y, u y * (fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)) v
          ∂(volume : Measure (Vec3 × ℝ)) := hchange
    _ = -∫ y, u y * (fderiv ℝ φ y) v ∂(volume : Measure (Vec3 × ℝ)) := by
      rw [show (fun y => u y * (fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)) v) =
          (fun y => -(u y * (fderiv ℝ φ y) v)) by
            funext y
            rw [hφDeriv]
            ring]
      rw [integral_neg]
    _ = ∫ y, g y * φ y ∂(volume : Measure (Vec3 × ℝ)) := by
      rw [hweakGlobal]
      simp
    _ = ∫ t, spaceTimeMollifier δ hδ t * g (z - t)
        ∂(volume : Measure (Vec3 × ℝ)) := hright.symm

/-- A local weak derivative identity determines the derivative of a mollification at points
whose kernel support stays inside the domain. This is used for the local energy identity in
`lem:caccioppoli`. -/
theorem spaceTimeMollify_fderiv_eq_of_local_weak
    {U : Set (Vec3 × ℝ)} {u g : Vec3 × ℝ → ℝ} {v : Vec3 × ℝ}
    (hU : IsOpen U)
    (hu : LocallyIntegrableOn u U (volume : Measure (Vec3 × ℝ)))
    (hg : LocallyIntegrableOn g U (volume : Measure (Vec3 × ℝ)))
    {δ : ℝ} (hδ : 0 < δ) {z : Vec3 × ℝ}
    (hz : Metric.closedBall z (3 * δ) ⊆ U)
    (hweak : ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.closedBall z (3 * δ) →
      (∫ y in U, u y * (fderiv ℝ φ y) v ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ y in U, g y * φ y ∂(volume : Measure (Vec3 × ℝ))) :
    HasFDerivAt (spaceTimeMollify u δ hδ)
        (fderiv ℝ (spaceTimeMollify u δ hδ) z) z ∧
      (fderiv ℝ (spaceTimeMollify u δ hδ) z) v = spaceTimeMollify g δ hδ z := by
  let K : Set (Vec3 × ℝ) := Metric.closedBall z (3 * δ)
  have hKcompact : IsCompact K := by
    exact isCompact_closedBall z (3 * δ)
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  have hKU : K ⊆ U := by
    simpa only [K] using hz
  have huKOn : IntegrableOn u K (volume : Measure (Vec3 × ℝ)) :=
    hu.integrableOn_compact_subset hKU hKcompact
  have hgKOn : IntegrableOn g K (volume : Measure (Vec3 × ℝ)) :=
    hg.integrableOn_compact_subset hKU hKcompact
  have huK : Integrable (K.indicator u) (volume : Measure (Vec3 × ℝ)) :=
    (integrable_indicator_iff hKmeas).2 huKOn
  have hgK : Integrable (K.indicator g) (volume : Measure (Vec3 × ℝ)) :=
    (integrable_indicator_iff hKmeas).2 hgKOn
  have hweakGlobal : ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ K →
      (∫ y, K.indicator u y * (fderiv ℝ φ y) v
        ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ y, K.indicator g y * φ y ∂(volume : Measure (Vec3 × ℝ)) := by
    intro φ hφ hφc hφK
    have hleft : (fun y : Vec3 × ℝ => K.indicator u y * (fderiv ℝ φ y) v) =
        U.indicator (fun y => u y * (fderiv ℝ φ y) v) := by
      funext y
      by_cases hy : y ∈ K
      · simp [hy, hKU hy]
      · have hnot : y ∉ tsupport φ := fun hmem => hy (hφK hmem)
        have hfd : fderiv ℝ φ y = 0 := fderiv_of_notMem_tsupport ℝ hnot
        have hfdv : (fderiv ℝ φ y) v = 0 := by rw [hfd]; simp
        simp [Set.indicator, hy, hfdv]
    have hright : (fun y : Vec3 × ℝ => K.indicator g y * φ y) =
        U.indicator (fun y => g y * φ y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [hy, hKU hy]
      · have hnot : y ∉ tsupport φ := fun hmem => hy (hφK hmem)
        have hφzero : φ y = 0 := image_eq_zero_of_notMem_tsupport hnot
        simp [Set.indicator, hy, hφzero]
    calc
      (∫ y, K.indicator u y * (fderiv ℝ φ y) v
          ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ y, U.indicator (fun y => u y * (fderiv ℝ φ y) v) y
          ∂(volume : Measure (Vec3 × ℝ)) := by rw [hleft]
      _ = ∫ y in U, u y * (fderiv ℝ φ y) v
          ∂(volume : Measure (Vec3 × ℝ)) := integral_indicator hU.measurableSet
      _ = -∫ y in U, g y * φ y ∂(volume : Measure (Vec3 × ℝ)) := hweak φ hφ hφc hφK
      _ = -∫ y, U.indicator (fun y => g y * φ y) y
          ∂(volume : Measure (Vec3 × ℝ)) := by rw [integral_indicator hU.measurableSet]
      _ = -∫ y, K.indicator g y * φ y ∂(volume : Measure (Vec3 × ℝ)) := by rw [hright]
  have hzK : Metric.closedBall z δ ⊆ K := by
    intro y hy
    rw [Metric.mem_closedBall] at hy ⊢
    exact le_trans hy (by linarith only [hδ])
  have hcomm := spaceTimeMollify_fderiv_eq_of_global_weak
    (U := K) (u := K.indicator u) (g := K.indicator g) (v := v)
    hweakGlobal huK.locallyIntegrable hδ hzK
  have hkernelTsupport : tsupport (spaceTimeMollifier δ hδ) =
      Metric.closedBall (0 : Vec3 × ℝ) δ := by
    simpa [spaceTimeMollifier, spaceTimeStandardBump] using
      (spaceTimeStandardBump δ hδ).tsupport_normed_eq
  have hconvEq (f : Vec3 × ℝ → ℝ) (q : Vec3 × ℝ)
      (hq : q ∈ Metric.ball z δ) :
      spaceTimeMollify (K.indicator f) δ hδ q = spaceTimeMollify f δ hδ q := by
    change (∫ t, spaceTimeMollifier δ hδ t * (K.indicator f) (q - t)
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ t, spaceTimeMollifier δ hδ t * f (q - t)
        ∂(volume : Measure (Vec3 × ℝ))
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases htk : spaceTimeMollifier δ hδ t = 0
    · simp [htk]
    · have hts : t ∈ tsupport (spaceTimeMollifier δ hδ) :=
        subset_tsupport _ (Function.mem_support.mpr htk)
      rw [hkernelTsupport, Metric.mem_closedBall] at hts
      have hmove : dist (q - t) q = dist t 0 := by
        simpa only [sub_zero] using dist_sub_left q t 0
      have hqz : dist q z < δ := Metric.mem_ball.mp hq
      have hdist : dist (q - t) z < 2 * δ := by
        calc
          dist (q - t) z ≤ dist (q - t) q + dist q z := dist_triangle _ _ _
          _ = dist t 0 + dist q z := by rw [hmove]
          _ ≤ δ + dist q z := by
            simpa [add_comm] using add_le_add_right hts (dist q z)
          _ < δ + δ := add_lt_add_of_le_of_lt le_rfl hqz
          _ = 2 * δ := by ring
      have hqK : q - t ∈ K := by
        rw [Metric.mem_closedBall]
        exact le_trans hdist.le (by linarith only [hδ])
      simp [hqK]
  have hEq : (fun q => spaceTimeMollify (K.indicator u) δ hδ q) =ᶠ[𝓝 z]
      spaceTimeMollify u δ hδ := by
    filter_upwards [Metric.ball_mem_nhds z hδ] with q hq
    exact hconvEq u q hq
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (spaceTimeMollify (K.indicator u) δ hδ) :=
    spaceTimeMollify_contDiff hδ huK.locallyIntegrable
  have hfdK : HasFDerivAt (spaceTimeMollify (K.indicator u) δ hδ)
      (fderiv ℝ (spaceTimeMollify (K.indicator u) δ hδ) z) z :=
    (hsmooth.differentiable (by simp) z).hasFDerivAt
  have hfd := hfdK.congr_of_eventuallyEq hEq.symm
  have hfdCanonical : HasFDerivAt (spaceTimeMollify u δ hδ)
      (fderiv ℝ (spaceTimeMollify u δ hδ) z) z := by
    have hfdMap : fderiv ℝ (spaceTimeMollify u δ hδ) z =
        fderiv ℝ (spaceTimeMollify (K.indicator u) δ hδ) z := hfd.fderiv
    simpa only [hfdMap] using hfd
  have hfdEq : (fderiv ℝ (spaceTimeMollify u δ hδ) z) v =
      (fderiv ℝ (spaceTimeMollify (K.indicator u) δ hδ) z) v := by
    exact congrArg (fun L : (Vec3 × ℝ) →L[ℝ] ℝ => L v) hfd.fderiv
  refine ⟨hfdCanonical, ?_⟩
  calc
    (fderiv ℝ (spaceTimeMollify u δ hδ) z) v =
        (fderiv ℝ (spaceTimeMollify (K.indicator u) δ hδ) z) v := hfdEq
    _ = spaceTimeMollify (K.indicator g) δ hδ z := hcomm
    _ = spaceTimeMollify g δ hδ z :=
      hconvEq g z (Metric.mem_ball.mpr (by simp [hδ]))

private theorem spatialPartial_eq_fderiv_of_hasFDerivAt
    {f : Vec3 × ℝ → ℝ} {L : (Vec3 × ℝ) →L[ℝ] ℝ} {z : Vec3 × ℝ}
    (hfd : HasFDerivAt f L z) (i : Fin 3) :
    spatialPartial (show ParabolicPoint → ℝ from f) i z = L (basisVec i, 0) := by
  let G : Vec3 → Vec3 × ℝ := fun x => (x, z.2)
  have hG : HasFDerivAt G
      ((ContinuousLinearMap.id ℝ Vec3).prod (0 : Vec3 →L[ℝ] ℝ)) z.1 := by
    exact (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) z.2 z.1)
  have hcomp := hfd.comp z.1 hG
  have hfun : (fun x : Vec3 => f (x, z.2)) = f ∘ G := rfl
  change (fderiv ℝ (fun x : Vec3 => f (x, z.2)) z.1) (basisVec i) = _
  rw [hfun, hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

private theorem timePartial_eq_fderiv_of_hasFDerivAt
    {f : Vec3 × ℝ → ℝ} {L : (Vec3 × ℝ) →L[ℝ] ℝ} {z : Vec3 × ℝ}
    (hfd : HasFDerivAt f L z) :
    timePartial (show ParabolicPoint → ℝ from f) z = L (0, 1) := by
  let G : ℝ → Vec3 × ℝ := fun s => (z.1, s)
  have hG : HasFDerivAt G
      ((0 : ℝ →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ ℝ)) z.2 := by
    exact (hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hcomp := hfd.comp z.2 hG
  have hfun : (fun s : ℝ => f (z.1, s)) = f ∘ G := rfl
  change (fderiv ℝ (fun s : ℝ => f (z.1, s)) z.2) 1 = _
  rw [hfun, hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

private theorem locallyIntegrableOn_parabolic_to_product
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {f : ParabolicPoint → ℝ}
    (hf : LocallyIntegrableOn f (spaceTimeSet Ω I) (volume : Measure ParabolicPoint)) :
    LocallyIntegrableOn (fun q : Vec3 × ℝ => f (parabolicHomeomorph.symm q))
      (Ω ×ˢ I) (volume : Measure (Vec3 × ℝ)) := by
  rw [locallyIntegrableOn_iff ((hΩ.prod hI).isLocallyClosed)]
  intro K hKU hK
  let Kp : Set ParabolicPoint := parabolicHomeomorph.symm '' K
  have hKp : IsCompact Kp := parabolicHomeomorph.symm.isCompact_image.mpr hK
  have hKpU : Kp ⊆ spaceTimeSet Ω I := by
    rintro p ⟨q, hq, rfl⟩
    have hqU := hKU hq
    change q.1 ∈ Ω ∧ q.2 ∈ I at hqU
    change q.1 ∈ Ω ∧ q.2 ∈ I
    exact hqU
  have hInt : IntegrableOn f Kp (volume : Measure ParabolicPoint) :=
    hf.integrableOn_compact_subset hKpU hKp
  exact (parabolicHomeomorphSymm_measurePreserving.integrableOn_image
    parabolicHomeomorph.symm.measurableEmbedding).mp hInt

/-- A continuous compactly supported real function is bounded. This supplies bounded
weights for the weighted pairing limits in `lem:caccioppoli`. -/
theorem continuous_hasCompactSupport_nnnorm_bound
    {X : Type*} [PseudoMetricSpace X] [Nonempty X] {f : X → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ C : NNReal, ∀ x, ‖f x‖₊ ≤ C := by
  have hbounded : Bornology.IsBounded (range f) := (hfc.isCompact_range hf).isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hbounded
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hRnonneg : 0 ≤ R := by
    have hx₀ := hR (Set.mem_range_self x₀)
    exact le_trans (norm_nonneg (f x₀)) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx₀)
  refine ⟨⟨R, hRnonneg⟩, fun x => ?_⟩
  apply NNReal.coe_le_coe.1
  change ‖f x‖ ≤ R
  have hx := hR (Set.mem_range_self x)
  simpa [Metric.mem_closedBall, dist_eq_norm] using hx

private theorem eLpNorm_mul_left_le_of_nnnorm_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    {C : NNReal} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) (p : ENNReal) :
    eLpNorm (fun x => f x * g x) p μ ≤ C • eLpNorm g p μ := by
  refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (hf.mul hg) ?_ p
  filter_upwards [hC] with x hx
  calc
    ‖f x * g x‖₊ = ‖f x‖₊ * ‖g x‖₊ := nnnorm_mul _ _
    _ ≤ C * ‖g x‖₊ := by gcongr

/-- Multiplication by a bounded measurable scalar preserves `L²` membership. -/
theorem memLp_mul_left_of_nnnorm_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    {C : NNReal} (hf : AEStronglyMeasurable f μ) (hg : MemLp g 2 μ)
    (hC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : MemLp (fun x => f x * g x) 2 μ := by
  apply hg.of_nnnorm_le_mul (c := C) (hf.mul hg.aestronglyMeasurable)
  filter_upwards [hC] with x hx
  calc
    ‖f x * g x‖₊ = ‖f x‖₊ * ‖g x‖₊ := nnnorm_mul _ _
    _ ≤ C * ‖g x‖₊ := by gcongr

/-- Multiplication by a bounded measurable scalar preserves strong `L²` convergence.
This is used to pass weighted energy pairings to the limit in `lem:caccioppoli`. -/
theorem tendsto_toLp_mul_left_of_nnnorm_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {φ : X → ℝ}
    {f : ℕ → X → ℝ} {g : X → ℝ} {C : NNReal}
    (hφ : AEStronglyMeasurable φ μ) (hC : ∀ x, ‖φ x‖₊ ≤ C)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto
      (fun n => (memLp_mul_left_of_nnnorm_bound hφ (hf n)
        (Filter.Eventually.of_forall hC)).toLp (fun x => φ x * f n x))
      atTop
      (𝓝 ((memLp_mul_left_of_nnnorm_bound hφ hg
        (Filter.Eventually.of_forall hC)).toLp (fun x => φ x * g x))) := by
  let hmul (n : ℕ) : MemLp (fun x => φ x * f n x) 2 μ :=
    memLp_mul_left_of_nnnorm_bound hφ (hf n) (Filter.Eventually.of_forall hC)
  let hmulG : MemLp (fun x => φ x * g x) 2 μ :=
    memLp_mul_left_of_nnnorm_bound hφ hg (Filter.Eventually.of_forall hC)
  have hprodBound (n : ℕ) :
      eLpNorm (fun x => φ x * (f n x - g x)) 2 μ ≤
        (C : ENNReal) * eLpNorm (f n - g) 2 μ := by
    have h := eLpNorm_mul_left_le_of_nnnorm_bound hφ
      ((hf n).sub hg).aestronglyMeasurable
      (Filter.Eventually.of_forall hC) 2
    simpa [ENNReal.smul_def] using h
  have hprodLimit : Tendsto
      (fun n => eLpNorm (fun x => φ x * (f n x - g x)) 2 μ) atTop (𝓝 0) := by
    have hscaled : Tendsto
        (fun n => (C : ENNReal) * eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := by
      convert ((ENNReal.continuous_mul_const (a := (C : ENNReal))
        ENNReal.coe_ne_top).continuousAt.tendsto.comp hconv) using 1
      · funext n
        simp [mul_comm]
      · simp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hscaled
    · filter_upwards [] with n
      exact (bot_le : (0 : ENNReal) ≤ eLpNorm (fun x => φ x * (f n x - g x)) 2 μ)
    · filter_upwards [] with n
      exact hprodBound n
  have hprodLimit' : Tendsto
      (fun n => eLpNorm ((fun x => φ x * f n x) - (fun x => φ x * g x)) 2 μ)
      atTop (𝓝 0) := by
    refine hprodLimit.congr' ?_
    filter_upwards [] with n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    ring
  have hreal : Tendsto
      (fun n => (eLpNorm ((fun x => φ x * f n x) - (fun x => φ x * g x)) 2 μ).toReal)
      atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => ((hmul n).sub hmulG).eLpNorm_ne_top)).2 hprodLimit'
  have hdist : Tendsto
      (fun n => dist ((hmul n).toLp (fun x => φ x * f n x))
        (hmulG.toLp (fun x => φ x * g x))) atTop (𝓝 0) := by
    refine hreal.congr' ?_
    filter_upwards [] with n
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [(hmul n).coeFn_toLp, hmulG.coeFn_toLp] with x hx hy
    change φ x * f n x - φ x * g x =
      (hmul n).toLp (fun x => φ x * f n x) x -
        hmulG.toLp (fun x => φ x * g x) x
    exact congrArg₂ (fun a b : ℝ => a - b) hx.symm hy.symm
  exact (tendsto_iff_dist_tendsto_zero).2 hdist

private theorem tendsto_toLp_of_eLpNorm_sub_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hreal : Tendsto (fun n => (eLpNorm (f n - g) 2 μ).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => ((hf n).sub hg).eLpNorm_ne_top)).2 hconv
  have hdist : Tendsto (fun n => dist ((hf n).toLp (f n)) (hg.toLp g)) atTop (𝓝 0) := by
    refine hreal.congr' ?_
    filter_upwards [] with n
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [(hf n).coeFn_toLp, hg.coeFn_toLp] with x hx hy
    exact congrArg₂ (fun a b : ℝ => a - b) hx.symm hy.symm
  exact (tendsto_iff_dist_tendsto_zero).2 hdist

private theorem parabolic_weak_spatial_to_product
    {Ω : Set Vec3} {I : Set ℝ} {δ : ℝ} {z : Vec3 × ℝ}
    (U : Set (Vec3 × ℝ)) (hU : U = Ω ×ˢ I)
    (hzU : Metric.closedBall z (3 * δ) ⊆ U)
    (w D : ParabolicPoint → ℝ) (j : Fin 3)
    (hweak : ∀ ψ : ParabolicPoint → ℝ, ψ ∈ spaceTimeTestFunction Ω I →
      (∫ p in spaceTimeSet Ω I, w p * spatialPartial ψ j p
        ∂(volume : Measure ParabolicPoint)) =
        -∫ p in spaceTimeSet Ω I, D p * ψ p ∂(volume : Measure ParabolicPoint))
    (φ : Vec3 × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφz : tsupport φ ⊆ Metric.closedBall z (3 * δ)) :
    (∫ y in U, w (parabolicHomeomorph.symm y) *
      (fderiv ℝ φ y) (basisVec j, 0) ∂(volume : Measure (Vec3 × ℝ))) =
      -∫ y in U, D (parabolicHomeomorph.symm y) * φ y
        ∂(volume : Measure (Vec3 × ℝ)) := by
  let φp : ParabolicPoint → ℝ := fun p => φ (parabolicHomeomorph p)
  have hφpEq : φp = (show ParabolicPoint → ℝ from φ) := by
    funext p
    rfl
  have htest : (show Vec3 × ℝ → ℝ from φp) ∈ spaceTimeTestFunction Ω I := by
    change (φp : Vec3 × ℝ → ℝ) ∈ spaceTimeTestFunction Ω I
    rw [hφpEq]
    exact ⟨hφ, hφc, hφz.trans (by simpa [hU, spaceTimeSet] using hzU)⟩
  have hsource := hweak φp htest
  have hleftTrans :
      (∫ p in spaceTimeSet Ω I, w p * spatialPartial φp j p
        ∂(volume : Measure ParabolicPoint)) =
      ∫ y in U, w (parabolicHomeomorph.symm y) *
        spatialPartial φp j (parabolicHomeomorph.symm y)
          ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [hU] using setIntegral_parabolic_to_product
      (F := fun p : ParabolicPoint => w p * spatialPartial φp j p)
  have hrightTrans :
      (∫ p in spaceTimeSet Ω I, D p * φp p ∂(volume : Measure ParabolicPoint)) =
      ∫ y in U, D (parabolicHomeomorph.symm y) * φ y
        ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [hU, φp, parabolicHomeomorph] using setIntegral_parabolic_to_product
      (F := fun p : ParabolicPoint => D p * φp p)
  have hfactor (y : Vec3 × ℝ) :
      spatialPartial φp j (parabolicHomeomorph.symm y) =
        (fderiv ℝ φ y) (basisVec j, 0) := by
    rw [hφpEq]
    simpa using spatialPartial_eq_joint_fderiv hφ y j
  calc
    (∫ y in U, w (parabolicHomeomorph.symm y) *
        (fderiv ℝ φ y) (basisVec j, 0) ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ y in U, w (parabolicHomeomorph.symm y) *
        spatialPartial φp j (parabolicHomeomorph.symm y)
          ∂(volume : Measure (Vec3 × ℝ)) := by
            apply integral_congr_ae
            filter_upwards [] with y
            rw [hfactor]
    _ = ∫ p in spaceTimeSet Ω I, w p * spatialPartial φp j p
        ∂(volume : Measure ParabolicPoint) := hleftTrans.symm
    _ = -∫ p in spaceTimeSet Ω I, D p * φp p
        ∂(volume : Measure ParabolicPoint) := hsource
    _ = -∫ y in U, D (parabolicHomeomorph.symm y) * φ y
        ∂(volume : Measure (Vec3 × ℝ)) := by rw [hrightTrans]

private theorem parabolic_weak_time_to_product
    {Ω : Set Vec3} {I : Set ℝ} {δ : ℝ} {z : Vec3 × ℝ}
    (U : Set (Vec3 × ℝ)) (hU : U = Ω ×ˢ I)
    (hzU : Metric.closedBall z (3 * δ) ⊆ U)
    (w D : ParabolicPoint → ℝ)
    (hweak : ∀ ψ : ParabolicPoint → ℝ, ψ ∈ spaceTimeTestFunction Ω I →
      (∫ p in spaceTimeSet Ω I, w p * timePartial ψ p
        ∂(volume : Measure ParabolicPoint)) =
        -∫ p in spaceTimeSet Ω I, D p * ψ p ∂(volume : Measure ParabolicPoint))
    (φ : Vec3 × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφz : tsupport φ ⊆ Metric.closedBall z (3 * δ)) :
    (∫ y in U, w (parabolicHomeomorph.symm y) *
      (fderiv ℝ φ y) (0, 1) ∂(volume : Measure (Vec3 × ℝ))) =
      -∫ y in U, D (parabolicHomeomorph.symm y) * φ y
        ∂(volume : Measure (Vec3 × ℝ)) := by
  let φp : ParabolicPoint → ℝ := fun p => φ (parabolicHomeomorph p)
  have hφpEq : φp = (show ParabolicPoint → ℝ from φ) := by
    funext p
    rfl
  have htest : (show Vec3 × ℝ → ℝ from φp) ∈ spaceTimeTestFunction Ω I := by
    change (φp : Vec3 × ℝ → ℝ) ∈ spaceTimeTestFunction Ω I
    rw [hφpEq]
    exact ⟨hφ, hφc, hφz.trans (by simpa [hU, spaceTimeSet] using hzU)⟩
  have hsource := hweak φp htest
  have hleftTrans :
      (∫ p in spaceTimeSet Ω I, w p * timePartial φp p
        ∂(volume : Measure ParabolicPoint)) =
      ∫ y in U, w (parabolicHomeomorph.symm y) *
        timePartial φp (parabolicHomeomorph.symm y)
          ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [hU] using setIntegral_parabolic_to_product
      (F := fun p : ParabolicPoint => w p * timePartial φp p)
  have hrightTrans :
      (∫ p in spaceTimeSet Ω I, D p * φp p ∂(volume : Measure ParabolicPoint)) =
      ∫ y in U, D (parabolicHomeomorph.symm y) * φ y
        ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [hU, φp, parabolicHomeomorph] using setIntegral_parabolic_to_product
      (F := fun p : ParabolicPoint => D p * φp p)
  have hfactor (y : Vec3 × ℝ) :
      timePartial φp (parabolicHomeomorph.symm y) = (fderiv ℝ φ y) (0, 1) := by
    rw [hφpEq]
    simpa using timePartial_eq_joint_fderiv hφ y
  calc
    (∫ y in U, w (parabolicHomeomorph.symm y) *
        (fderiv ℝ φ y) (0, 1) ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ y in U, w (parabolicHomeomorph.symm y) *
        timePartial φp (parabolicHomeomorph.symm y)
          ∂(volume : Measure (Vec3 × ℝ)) := by
            apply integral_congr_ae
            filter_upwards [] with y
            rw [hfactor]
    _ = ∫ p in spaceTimeSet Ω I, w p * timePartial φp p
        ∂(volume : Measure ParabolicPoint) := hleftTrans.symm
    _ = -∫ p in spaceTimeSet Ω I, D p * φp p
        ∂(volume : Measure ParabolicPoint) := hsource
    _ = -∫ y in U, D (parabolicHomeomorph.symm y) * φ y
        ∂(volume : Measure (Vec3 × ℝ)) := by rw [hrightTrans]

/-- Mollification commutes componentwise with the spatial, second spatial, and time weak
derivatives on compact subsets of an open space-time domain (manuscript `def:sws`). -/
theorem spaceTimeMollify_weak_derivatives
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    {δ : ℝ} (hδ : 0 < δ) {z : Vec3 × ℝ}
    (hz : Metric.closedBall z (4 * δ) ⊆ Ω ×ˢ I) :
    (∀ i j : Fin 3,
      spatialPartial (show ParabolicPoint → ℝ from
        fun q => spaceTimeMollify
          (fun y => w (parabolicHomeomorph.symm y) i) δ hδ q) j z =
        spaceTimeMollify (fun y => Dw (parabolicHomeomorph.symm y) i j) δ hδ z) ∧
    (∀ i j k : Fin 3,
      spatialSecondPartial (show ParabolicPoint → ℝ from
        fun q => spaceTimeMollify
          (fun y => w (parabolicHomeomorph.symm y) i) δ hδ q) j k z =
        spaceTimeMollify (fun y => D2w (parabolicHomeomorph.symm y) i j k) δ hδ z) ∧
    (∀ i : Fin 3,
      timePartial (show ParabolicPoint → ℝ from
        fun q => spaceTimeMollify
          (fun y => w (parabolicHomeomorph.symm y) i) δ hδ q) z =
        spaceTimeMollify (fun y => Dtw (parabolicHomeomorph.symm y) i) δ hδ z) := by
  rcases hderiv with ⟨hw, hDw, hD2w, hDtw, hweak⟩
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  have hUopen : IsOpen U := by exact hΩ.prod hI
  have hz4 : Metric.closedBall z (4 * δ) ⊆ U := by simpa [U] using hz
  have hz3 : Metric.closedBall z (3 * δ) ⊆ U := by
    intro q hq
    apply hz4
    rw [Metric.mem_closedBall] at hq ⊢
    exact le_trans hq (by linarith only [hδ])
  have hwi (i : Fin 3) :
      LocallyIntegrableOn (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q) i) U
        (volume : Measure (Vec3 × ℝ)) := by
    have hpara : LocallyIntegrableOn (fun p : ParabolicPoint => w p i)
        (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) := by
      exact locallyIntegrableOn_pi_eval hw i
    simpa [U] using locallyIntegrableOn_parabolic_to_product hΩ hI hpara
  have hDwij (i j : Fin 3) :
      LocallyIntegrableOn (fun q : Vec3 × ℝ => Dw (parabolicHomeomorph.symm q) i j) U
        (volume : Measure (Vec3 × ℝ)) := by
    have hpara : LocallyIntegrableOn (fun p : ParabolicPoint => Dw p i j)
        (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) := by
      have hi : LocallyIntegrableOn (fun p : ParabolicPoint => Dw p i)
          (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) := by
        exact locallyIntegrableOn_pi_eval hDw i
      exact locallyIntegrableOn_pi_eval hi j
    simpa [U] using locallyIntegrableOn_parabolic_to_product hΩ hI hpara
  have hD2wijk (i j k : Fin 3) :
      LocallyIntegrableOn (fun q : Vec3 × ℝ => D2w (parabolicHomeomorph.symm q) i j k) U
        (volume : Measure (Vec3 × ℝ)) := by
    have hpara : LocallyIntegrableOn (fun p : ParabolicPoint => D2w p i j k)
        (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) := by
      have hi : LocallyIntegrableOn (fun p : ParabolicPoint => D2w p i)
          (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) := by
        exact locallyIntegrableOn_pi_eval hD2w i
      have hij : LocallyIntegrableOn (fun p : ParabolicPoint => D2w p i j)
          (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) := by
        exact locallyIntegrableOn_pi_eval hi j
      exact locallyIntegrableOn_pi_eval hij k
    simpa [U] using locallyIntegrableOn_parabolic_to_product hΩ hI hpara
  have hDtw_i (i : Fin 3) :
      LocallyIntegrableOn (fun q : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm q) i) U
        (volume : Measure (Vec3 × ℝ)) := by
    have hpara : LocallyIntegrableOn (fun p : ParabolicPoint => Dtw p i)
        (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) := by
      exact locallyIntegrableOn_pi_eval hDtw i
    simpa [U] using locallyIntegrableOn_parabolic_to_product hΩ hI hpara
  have hweakSpatial (q : Vec3 × ℝ) (hqU : Metric.closedBall q (3 * δ) ⊆ U)
      (i j : Fin 3) :
      ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.closedBall q (3 * δ) →
        (∫ y in U, w (parabolicHomeomorph.symm y) i *
          (fderiv ℝ φ y) (basisVec j, 0) ∂(volume : Measure (Vec3 × ℝ))) =
          -∫ y in U, Dw (parabolicHomeomorph.symm y) i j * φ y
            ∂(volume : Measure (Vec3 × ℝ)) := by
    intro φ hφ hφc hφq
    exact parabolic_weak_spatial_to_product U rfl
      hqU
      (fun p => w p i)
      (fun p => Dw p i j) j
      (fun ψ htest => (hweak ψ htest).1 i j)
      φ hφ hφc hφq
  have hweakSecond (q : Vec3 × ℝ) (hqU : Metric.closedBall q (3 * δ) ⊆ U)
      (i j k : Fin 3) :
      ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.closedBall q (3 * δ) →
        (∫ y in U, Dw (parabolicHomeomorph.symm y) i j *
          (fderiv ℝ φ y) (basisVec k, 0) ∂(volume : Measure (Vec3 × ℝ))) =
          -∫ y in U, D2w (parabolicHomeomorph.symm y) i j k * φ y
            ∂(volume : Measure (Vec3 × ℝ)) := by
    intro φ hφ hφc hφq
    exact parabolic_weak_spatial_to_product U rfl hqU
      (fun p => Dw p i j)
      (fun p => D2w p i j k) k
      (fun ψ htest => (hweak ψ htest).2.1 i j k)
      φ hφ hφc hφq
  have hweakTime (q : Vec3 × ℝ) (hqU : Metric.closedBall q (3 * δ) ⊆ U)
      (i : Fin 3) :
      ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.closedBall q (3 * δ) →
        (∫ y in U, w (parabolicHomeomorph.symm y) i *
          (fderiv ℝ φ y) (0, 1) ∂(volume : Measure (Vec3 × ℝ))) =
          -∫ y in U, Dtw (parabolicHomeomorph.symm y) i * φ y
            ∂(volume : Measure (Vec3 × ℝ)) := by
    intro φ hφ hφc hφq
    exact parabolic_weak_time_to_product U rfl hqU
      (fun p => w p i)
      (fun p => Dtw p i)
      (fun ψ htest => (hweak ψ htest).2.2 i)
      φ hφ hφc hφq
  refine ⟨?_, ?_⟩
  · intro i j
    have hcomm := spaceTimeMollify_fderiv_eq_of_local_weak
      (u := fun y => w (parabolicHomeomorph.symm y) i)
      (g := fun y => Dw (parabolicHomeomorph.symm y) i j)
      (v := (basisVec j, 0)) hUopen (hwi i) (hDwij i j) hδ hz3
      (hweakSpatial z hz3 i j)
    rw [spatialPartial_eq_fderiv_of_hasFDerivAt hcomm.1 j, hcomm.2]
  · refine ⟨?_, ?_⟩
    · intro i j k
      have hsecond := spaceTimeMollify_fderiv_eq_of_local_weak
        (u := fun y => Dw (parabolicHomeomorph.symm y) i j)
        (g := fun y => D2w (parabolicHomeomorph.symm y) i j k)
        (v := (basisVec k, 0)) hUopen (hDwij i j) (hD2wijk i j k) hδ hz3
        (hweakSecond z hz3 i j k)
      have hfirstNear :
          (fun y => spatialPartial (show ParabolicPoint → ℝ from
            fun q => spaceTimeMollify
              (fun p => w (parabolicHomeomorph.symm p) i) δ hδ q) j y) =ᶠ[𝓝 z]
          (fun y => spaceTimeMollify
            (fun p => Dw (parabolicHomeomorph.symm p) i j) δ hδ y) := by
        filter_upwards [Metric.ball_mem_nhds z hδ] with y hy
        have hyz : dist y z < δ := Metric.mem_ball.mp hy
        have hybuffer : Metric.closedBall y (3 * δ) ⊆ U := by
          intro q hq
          apply hz4
          rw [Metric.mem_closedBall] at hq ⊢
          calc
            dist q z ≤ dist q y + dist y z := dist_triangle _ _ _
            _ ≤ 4 * δ := by linarith only [hq, hyz]
        have hcommY := spaceTimeMollify_fderiv_eq_of_local_weak
          (u := fun p => w (parabolicHomeomorph.symm p) i)
          (g := fun p => Dw (parabolicHomeomorph.symm p) i j)
          (v := (basisVec j, 0)) hUopen (hwi i) (hDwij i j) hδ hybuffer
          (hweakSpatial y hybuffer i j)
        calc
          spatialPartial (show ParabolicPoint → ℝ from fun q =>
              spaceTimeMollify
                (fun p => w (parabolicHomeomorph.symm p) i) δ hδ q) j y =
              (fderiv ℝ (spaceTimeMollify
                (fun p => w (parabolicHomeomorph.symm p) i) δ hδ) y) (basisVec j, 0) :=
                spatialPartial_eq_fderiv_of_hasFDerivAt hcommY.1 j
          _ = spaceTimeMollify
              (fun p => Dw (parabolicHomeomorph.symm p) i j) δ hδ y := hcommY.2
      have houter := hsecond.1.congr_of_eventuallyEq hfirstNear
      change spatialPartial (fun y => spatialPartial
        (show ParabolicPoint → ℝ from fun q => spaceTimeMollify
          (fun p => w (parabolicHomeomorph.symm p) i) δ hδ q) j y) k z = _
      rw [spatialPartial_eq_fderiv_of_hasFDerivAt houter k, hsecond.2]
    · intro i
      have hcomm := spaceTimeMollify_fderiv_eq_of_local_weak
        (u := fun y => w (parabolicHomeomorph.symm y) i)
        (g := fun y => Dtw (parabolicHomeomorph.symm y) i)
        (v := (0, 1)) hUopen (hwi i) (hDtw_i i) hδ hz3
        (hweakTime z hz3 i)
      rw [timePartial_eq_fderiv_of_hasFDerivAt hcomm.1, hcomm.2]

private theorem hasSpaceTimeWeakDerivs_indicator
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs Ω I
      ((spaceTimeSet Ω I).indicator w)
      ((spaceTimeSet Ω I).indicator Dw)
      ((spaceTimeSet Ω I).indicator D2w)
      ((spaceTimeSet Ω I).indicator Dtw) := by
  let V : Set ParabolicPoint := spaceTimeSet Ω I
  let w₀ : ParabolicPoint → Vec3 := V.indicator w
  let Dw₀ : ParabolicPoint → Fin 3 → Vec3 := V.indicator Dw
  let D2w₀ : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := V.indicator D2w
  let Dtw₀ : ParabolicPoint → Vec3 := V.indicator Dtw
  have hVmeas : MeasurableSet V := by
    dsimp [V, spaceTimeSet]
    exact hΩ.measurableSet.prod hI.measurableSet
  have hEqw : w =ᵐ[volume.restrict V] w₀ := by
    filter_upwards [ae_restrict_mem hVmeas] with p hp
    simp [w₀, hp]
  have hEqDw : Dw =ᵐ[volume.restrict V] Dw₀ := by
    filter_upwards [ae_restrict_mem hVmeas] with p hp
    simp [Dw₀, hp]
  have hEqD2w : D2w =ᵐ[volume.restrict V] D2w₀ := by
    filter_upwards [ae_restrict_mem hVmeas] with p hp
    simp [D2w₀, hp]
  have hEqDtw : Dtw =ᵐ[volume.restrict V] Dtw₀ := by
    filter_upwards [ae_restrict_mem hVmeas] with p hp
    simp [Dtw₀, hp]
  rcases hderiv with ⟨hw, hDw, hD2w, hDtw, hweak⟩
  have hderiv₀ : HasSpaceTimeWeakDerivs Ω I w₀ Dw₀ D2w₀ Dtw₀ := by
    refine ⟨hw.congr hEqw, hDw.congr hEqDw, hD2w.congr hEqD2w,
      hDtw.congr hEqDtw, ?_⟩
    intro ψ hψ
    rcases hweak ψ hψ with ⟨hsp, hsec, htime⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      have hleft :
          (∫ p in V, w₀ p i * spatialPartial ψ j p ∂(volume : Measure ParabolicPoint)) =
            ∫ p in V, w p i * spatialPartial ψ j p ∂(volume : Measure ParabolicPoint) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hVmeas] with p hp
        simp [w₀, hp]
      have hright :
          (∫ p in V, Dw₀ p i j * ψ p ∂(volume : Measure ParabolicPoint)) =
            ∫ p in V, Dw p i j * ψ p ∂(volume : Measure ParabolicPoint) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hVmeas] with p hp
        simp [Dw₀, hp]
      calc
        ∫ p in V, w₀ p i * spatialPartial ψ j p ∂(volume : Measure ParabolicPoint) =
            ∫ p in V, w p i * spatialPartial ψ j p ∂(volume : Measure ParabolicPoint) := hleft
        _ = -∫ p in V, Dw p i j * ψ p ∂(volume : Measure ParabolicPoint) := hsp i j
        _ = -∫ p in V, Dw₀ p i j * ψ p ∂(volume : Measure ParabolicPoint) := by rw [hright]
    · intro i j k
      have hleft :
          (∫ p in V, Dw₀ p i j * spatialPartial ψ k p ∂(volume : Measure ParabolicPoint)) =
            ∫ p in V, Dw p i j * spatialPartial ψ k p ∂(volume : Measure ParabolicPoint) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hVmeas] with p hp
        simp [Dw₀, hp]
      have hright :
          (∫ p in V, D2w₀ p i j k * ψ p ∂(volume : Measure ParabolicPoint)) =
            ∫ p in V, D2w p i j k * ψ p ∂(volume : Measure ParabolicPoint) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hVmeas] with p hp
        simp [D2w₀, hp]
      calc
        ∫ p in V, Dw₀ p i j * spatialPartial ψ k p ∂(volume : Measure ParabolicPoint) =
            ∫ p in V, Dw p i j * spatialPartial ψ k p ∂(volume : Measure ParabolicPoint) := hleft
        _ = -∫ p in V, D2w p i j k * ψ p ∂(volume : Measure ParabolicPoint) := hsec i j k
        _ = -∫ p in V, D2w₀ p i j k * ψ p ∂(volume : Measure ParabolicPoint) := by rw [hright]
    · intro i
      have hleft :
          (∫ p in V, w₀ p i * timePartial ψ p ∂(volume : Measure ParabolicPoint)) =
            ∫ p in V, w p i * timePartial ψ p ∂(volume : Measure ParabolicPoint) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hVmeas] with p hp
        simp [w₀, hp]
      have hright :
          (∫ p in V, Dtw₀ p i * ψ p ∂(volume : Measure ParabolicPoint)) =
            ∫ p in V, Dtw p i * ψ p ∂(volume : Measure ParabolicPoint) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hVmeas] with p hp
        simp [Dtw₀, hp]
      calc
        ∫ p in V, w₀ p i * timePartial ψ p ∂(volume : Measure ParabolicPoint) =
            ∫ p in V, w p i * timePartial ψ p ∂(volume : Measure ParabolicPoint) := hleft
        _ = -∫ p in V, Dtw p i * ψ p ∂(volume : Measure ParabolicPoint) := htime i
        _ = -∫ p in V, Dtw₀ p i * ψ p ∂(volume : Measure ParabolicPoint) := by rw [hright]
  exact hderiv₀

private theorem mollified_square_time_identity
    {u g φ : Vec3 × ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hcomm : ∀ q ∈ tsupport φ,
      timePartial (show ParabolicPoint → ℝ from u) (parabolicHomeomorph.symm q) = g q) :
    (∫ q : Vec3 × ℝ, u q ^ 2 * (fderiv ℝ φ q) (0, 1)
      ∂(volume : Measure (Vec3 × ℝ))) =
      -(2 * ∫ q : Vec3 × ℝ, u q * (φ q * g q)
        ∂(volume : Measure (Vec3 × ℝ))) := by
  have hIBP := CKN.integral_mul_timePartial_eq_neg_timePartial_mul
    (show ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => u q * u q) from hu.mul hu)
    hφ hφc
  have htimeSq (q : Vec3 × ℝ) :
      timePartial (show ParabolicPoint → ℝ from fun p => u p * u p) q =
        2 * u q * timePartial (show ParabolicPoint → ℝ from u) q := by
    have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z * u z) := hu.mul hu
    have hprod := timePartial_eq_joint_fderiv
      (g := fun z : Vec3 × ℝ => u z * u z) hsq q
    have hsingle := timePartial_eq_joint_fderiv (g := u) hu q
    calc
      timePartial (show ParabolicPoint → ℝ from fun p => u p * u p) q =
          fderiv ℝ (fun z : Vec3 × ℝ => u z * u z) q (0, 1) := hprod
      _ = 2 * u q * fderiv ℝ u q (0, 1) := by
        rw [fderiv_fun_mul (hu.differentiable (by simp) q)
          (hu.differentiable (by simp) q)]
        simp only [add_apply, smul_apply]
        ring
      _ = 2 * u q * timePartial (show ParabolicPoint → ℝ from u) q := by rw [← hsingle]
  have hmul (q : Vec3 × ℝ) :
      timePartial (show ParabolicPoint → ℝ from fun z => u z * u z) q * φ q =
        2 * (u q * (φ q * g q)) := by
    by_cases hq : q ∈ tsupport φ
    · have hcomm' :
          timePartial (show ParabolicPoint → ℝ from u) q = g q := by
        simpa only [parabolicHomeomorph_symm_apply] using hcomm q hq
      rw [htimeSq q, hcomm']
      ring
    · have hφzero : φ q = 0 := image_eq_zero_of_notMem_tsupport hq
      simp [hφzero]
  calc
    (∫ q : Vec3 × ℝ, u q ^ 2 * (fderiv ℝ φ q) (0, 1)
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ q : Vec3 × ℝ, u q * u q *
        timePartial (show ParabolicPoint → ℝ from φ) q
          ∂(volume : Measure (Vec3 × ℝ)) := by
            apply integral_congr_ae
            filter_upwards [] with q
            rw [timePartial_eq_joint_fderiv hφ q]
            ring
    _ = -∫ q : Vec3 × ℝ,
        timePartial (show ParabolicPoint → ℝ from fun z => u z * u z) q * φ q
          ∂(volume : Measure (Vec3 × ℝ)) := hIBP
    _ = -(2 * ∫ q : Vec3 × ℝ, u q * (φ q * g q)
          ∂(volume : Measure (Vec3 × ℝ))) := by
            congr 1
            calc
              (∫ q : Vec3 × ℝ,
                  timePartial (show ParabolicPoint → ℝ from fun z => u z * u z) q * φ q
                    ∂(volume : Measure (Vec3 × ℝ))) =
                ∫ q : Vec3 × ℝ, 2 * (u q * (φ q * g q))
                  ∂(volume : Measure (Vec3 × ℝ)) := by
                    apply integral_congr_ae
                    filter_upwards [] with q
                    exact hmul q
              _ = 2 * ∫ q : Vec3 × ℝ, u q * (φ q * g q)
                  ∂(volume : Measure (Vec3 × ℝ)) := by rw [integral_const_mul]

private theorem inner_real_toLp_eq_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hpoint : ∀ x, f x * g x = h x) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, h x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]
  simp only [Real.inner_apply]
  exact hpoint x

/-- The square of a locally square-integrable weak solution has the expected weak time
derivative on compactly supported tests (manuscript `def:sws`). The formula is written as
the finite sum of scalar pairings; `u` and `g` are the zero extensions of `w` and `Dtw`.
The buffer condition keeps every mollification kernel inside the weak-derivative domain. -/
theorem weak_time_derivative_sq
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hL2w : ∀ i : Fin 3,
      MemLp (fun q : Vec3 × ℝ =>
        ((spaceTimeSet Ω I).indicator w (parabolicHomeomorph.symm q)) i)
        2 (volume : Measure (Vec3 × ℝ)))
    (hL2time : ∀ i : Fin 3,
      MemLp (fun q : Vec3 × ℝ =>
        ((spaceTimeSet Ω I).indicator Dtw (parabolicHomeomorph.symm q)) i)
        2 (volume : Measure (Vec3 × ℝ)))
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hbuffer : ∀ q ∈ tsupport φ, Metric.closedBall q (4 * δ₀) ⊆ Ω ×ˢ I) :
    (∑ i : Fin 3,
      ∫ q : Vec3 × ℝ,
        (((spaceTimeSet Ω I).indicator w (parabolicHomeomorph.symm q)) i) ^ 2 *
          (fderiv ℝ φ q) (0, 1) ∂(volume : Measure (Vec3 × ℝ))) =
      -(2 * ∑ i : Fin 3,
        ∫ q : Vec3 × ℝ,
          ((spaceTimeSet Ω I).indicator w (parabolicHomeomorph.symm q)) i *
          ((spaceTimeSet Ω I).indicator Dtw (parabolicHomeomorph.symm q)) i *
          φ q ∂(volume : Measure (Vec3 × ℝ))) := by
  let V : Set ParabolicPoint := spaceTimeSet Ω I
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let w₀ : ParabolicPoint → Vec3 := V.indicator w
  let Dw₀ : ParabolicPoint → Fin 3 → Vec3 := V.indicator Dw
  let D2w₀ : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := V.indicator D2w
  let Dtw₀ : ParabolicPoint → Vec3 := V.indicator Dtw
  let u : Fin 3 → Vec3 × ℝ → ℝ := fun i q => w₀ (parabolicHomeomorph.symm q) i
  let g : Fin 3 → Vec3 × ℝ → ℝ := fun i q => Dtw₀ (parabolicHomeomorph.symm q) i
  have hderiv₀ := hasSpaceTimeWeakDerivs_indicator hΩ hI hderiv
  have hL2u (i : Fin 3) : MemLp (u i) 2 (volume : Measure (Vec3 × ℝ)) := by
    exact hL2w i
  have hL2g (i : Fin 3) : MemLp (g i) 2 (volume : Measure (Vec3 × ℝ)) := by
    exact hL2time i
  let δ : ℕ → ℝ := fun n => δ₀ / (n + 1 : ℝ)
  have hδpos (n : ℕ) : 0 < δ n := by
    apply div_pos hδ₀
    positivity
  have hδle (n : ℕ) : δ n ≤ δ₀ := by
    apply div_le_self hδ₀.le
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith only [hn]
  have hδtendsto : Tendsto δ atTop (𝓝 0) := by
    simpa [δ, div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  let uε (i : Fin 3) (n : ℕ) : Vec3 × ℝ → ℝ := spaceTimeMollify (u i) (δ n) (hδpos n)
  let gε (i : Fin 3) (n : ℕ) : Vec3 × ℝ → ℝ := spaceTimeMollify (g i) (δ n) (hδpos n)
  have hUεsmooth (i : Fin 3) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (uε i n) := by
    apply spaceTimeMollify_contDiff (hδpos n)
    exact (hL2u i).locallyIntegrable (by norm_num)
  have hGεsmooth (i : Fin 3) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (gε i n) := by
    apply spaceTimeMollify_contDiff (hδpos n)
    exact (hL2g i).locallyIntegrable (by norm_num)
  have hUεmem (i : Fin 3) (n : ℕ) : MemLp (uε i n) 2 (volume : Measure (Vec3 × ℝ)) := by
    exact (spaceTimeMollify_eLpNorm_le (hδpos n) (hL2u i)).trans_lt (hL2u i).eLpNorm_lt_top
  have hGεmem (i : Fin 3) (n : ℕ) : MemLp (gε i n) 2 (volume : Measure (Vec3 × ℝ)) := by
    exact (spaceTimeMollify_eLpNorm_le (hδpos n) (hL2g i)).trans_lt (hL2g i).eLpNorm_lt_top
  have hUεconv (i : Fin 3) :
      Tendsto (fun n => eLpNorm (uε i n - u i) 2 (volume : Measure (Vec3 × ℝ)))
        atTop (𝓝 0) := by
    change Tendsto (fun n => eLpNorm
      (fun q => spaceTimeMollify (u i) (δ n) (hδpos n) q - u i q) 2
        (volume : Measure (Vec3 × ℝ))) atTop (𝓝 0)
    exact tendsto_eLpNorm_sub_zero_spaceTimeMollify (hL2u i) hδtendsto hδpos
  have hGεconv (i : Fin 3) :
      Tendsto (fun n => eLpNorm (gε i n - g i) 2 (volume : Measure (Vec3 × ℝ)))
        atTop (𝓝 0) := by
    change Tendsto (fun n => eLpNorm
      (fun q => spaceTimeMollify (g i) (δ n) (hδpos n) q - g i q) 2
        (volume : Measure (Vec3 × ℝ))) atTop (𝓝 0)
    exact tendsto_eLpNorm_sub_zero_spaceTimeMollify (hL2g i) hδtendsto hδpos
  let ψ : Vec3 × ℝ → ℝ := fun q => (fderiv ℝ φ q) (0, 1)
  have hψcont : Continuous ψ := by
    dsimp [ψ]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψc : HasCompactSupport ψ := by
    dsimp [ψ]
    exact hφc.fderiv_apply (𝕜 := ℝ) (0, 1)
  obtain ⟨Cψ, hCψ⟩ := continuous_hasCompactSupport_nnnorm_bound hψcont hψc
  obtain ⟨Cφ, hCφ⟩ := continuous_hasCompactSupport_nnnorm_bound hφ.continuous hφc
  have hψmeas : AEStronglyMeasurable ψ (volume : Measure (Vec3 × ℝ)) :=
    hψcont.measurable.aestronglyMeasurable
  have hφmeas : AEStronglyMeasurable φ (volume : Measure (Vec3 × ℝ)) :=
    hφ.continuous.measurable.aestronglyMeasurable
  have hUεLp (i : Fin 3) :
      Tendsto (fun n => (hUεmem i n).toLp (uε i n)) atTop
        (𝓝 ((hL2u i).toLp (u i))) :=
    tendsto_toLp_of_eLpNorm_sub_zero (hUεmem i) (hL2u i) (hUεconv i)
  have hGεLp (i : Fin 3) :
      Tendsto (fun n => (hGεmem i n).toLp (gε i n)) atTop
        (𝓝 ((hL2g i).toLp (g i))) :=
    tendsto_toLp_of_eLpNorm_sub_zero (hGεmem i) (hL2g i) (hGεconv i)
  have hψεULp (i : Fin 3) :
      Tendsto
        (fun n => (memLp_mul_left_of_nnnorm_bound hψmeas (hUεmem i n)
          (Filter.Eventually.of_forall hCψ)).toLp (fun q => ψ q * uε i n q)) atTop
        (𝓝 ((memLp_mul_left_of_nnnorm_bound hψmeas (hL2u i)
          (Filter.Eventually.of_forall hCψ)).toLp (fun q => ψ q * u i q))) :=
    tendsto_toLp_mul_left_of_nnnorm_bound hψmeas hCψ (fun n => hUεmem i n)
      (hL2u i) (hUεconv i)
  have hφGεLp (i : Fin 3) :
      Tendsto
        (fun n => (memLp_mul_left_of_nnnorm_bound hφmeas (hGεmem i n)
          (Filter.Eventually.of_forall hCφ)).toLp (fun q => φ q * gε i n q)) atTop
        (𝓝 ((memLp_mul_left_of_nnnorm_bound hφmeas (hL2g i)
          (Filter.Eventually.of_forall hCφ)).toLp (fun q => φ q * g i q))) :=
    tendsto_toLp_mul_left_of_nnnorm_bound hφmeas hCφ (fun n => hGεmem i n)
      (hL2g i) (hGεconv i)
  have hAconv (i : Fin 3) :
      Tendsto (fun n => inner ℝ ((hUεmem i n).toLp (uε i n))
        ((memLp_mul_left_of_nnnorm_bound hψmeas (hUεmem i n)
          (Filter.Eventually.of_forall hCψ)).toLp (fun q => ψ q * uε i n q))) atTop
        (𝓝 (inner ℝ ((hL2u i).toLp (u i))
          ((memLp_mul_left_of_nnnorm_bound hψmeas (hL2u i)
            (Filter.Eventually.of_forall hCψ)).toLp (fun q => ψ q * u i q)))) := by
    exact (continuous_inner.tendsto _).comp ((hUεLp i).prodMk_nhds (hψεULp i))
  have hBconv (i : Fin 3) :
      Tendsto (fun n => inner ℝ ((hUεmem i n).toLp (uε i n))
        ((memLp_mul_left_of_nnnorm_bound hφmeas (hGεmem i n)
          (Filter.Eventually.of_forall hCφ)).toLp (fun q => φ q * gε i n q))) atTop
        (𝓝 (inner ℝ ((hL2u i).toLp (u i))
          ((memLp_mul_left_of_nnnorm_bound hφmeas (hL2g i)
            (Filter.Eventually.of_forall hCφ)).toLp (fun q => φ q * g i q)))) := by
    exact (continuous_inner.tendsto _).comp ((hUεLp i).prodMk_nhds (hφGεLp i))
  have hcomponent (i : Fin 3) (n : ℕ) :
      (∫ q : Vec3 × ℝ, uε i n q ^ 2 * ψ q ∂(volume : Measure (Vec3 × ℝ))) =
        -(2 * ∫ q : Vec3 × ℝ, uε i n q * (φ q * gε i n q)
          ∂(volume : Measure (Vec3 × ℝ))) := by
    have hcomm (q : Vec3 × ℝ) (hq : q ∈ tsupport φ) :
        timePartial (show ParabolicPoint → ℝ from uε i n)
            (parabolicHomeomorph.symm q) = gε i n q := by
      have hresult := spaceTimeMollify_weak_derivatives hΩ hI hderiv₀
        (hδpos n) (z := q) (by
          intro y hy
          exact hbuffer q hq ((Metric.closedBall_subset_closedBall
            (mul_le_mul_of_nonneg_left (hδle n) (by norm_num : 0 ≤ (4 : ℝ)))) hy))
      have hraw := hresult.2.2 i
      simpa [u, g, uε, gε, w₀, Dtw₀, V, parabolicHomeomorph_symm_apply] using hraw
    simpa [ψ] using mollified_square_time_identity (hUεsmooth i n) hφ hφc hcomm
  have hAeq (i : Fin 3) (n : ℕ) :
      inner ℝ ((hUεmem i n).toLp (uε i n))
        ((memLp_mul_left_of_nnnorm_bound hψmeas (hUεmem i n)
          (Filter.Eventually.of_forall hCψ)).toLp (fun q => ψ q * uε i n q)) =
        ∫ q : Vec3 × ℝ, uε i n q ^ 2 * ψ q ∂(volume : Measure (Vec3 × ℝ)) := by
    exact inner_real_toLp_eq_integral (hUεmem i n)
      (memLp_mul_left_of_nnnorm_bound hψmeas (hUεmem i n)
        (Filter.Eventually.of_forall hCψ)) (fun q => by ring)
  have hBeq (i : Fin 3) (n : ℕ) :
      inner ℝ ((hUεmem i n).toLp (uε i n))
        ((memLp_mul_left_of_nnnorm_bound hφmeas (hGεmem i n)
          (Filter.Eventually.of_forall hCφ)).toLp (fun q => φ q * gε i n q)) =
        ∫ q : Vec3 × ℝ, uε i n q * (φ q * gε i n q)
          ∂(volume : Measure (Vec3 × ℝ)) := by
    exact inner_real_toLp_eq_integral (hUεmem i n)
      (memLp_mul_left_of_nnnorm_bound hφmeas (hGεmem i n)
        (Filter.Eventually.of_forall hCφ)) (fun _ => rfl)
  have hAlim (i : Fin 3) :
      Tendsto (fun n => ∫ q : Vec3 × ℝ, uε i n q ^ 2 * ψ q
        ∂(volume : Measure (Vec3 × ℝ))) atTop
        (𝓝 (∫ q : Vec3 × ℝ, u i q ^ 2 * ψ q ∂(volume : Measure (Vec3 × ℝ)))) := by
    have hAeqLimit : inner ℝ ((hL2u i).toLp (u i))
        ((memLp_mul_left_of_nnnorm_bound hψmeas (hL2u i)
          (Filter.Eventually.of_forall hCψ)).toLp (fun q => ψ q * u i q)) =
        ∫ q : Vec3 × ℝ, u i q ^ 2 * ψ q ∂(volume : Measure (Vec3 × ℝ)) := by
      exact inner_real_toLp_eq_integral (hL2u i)
        (memLp_mul_left_of_nnnorm_bound hψmeas (hL2u i)
          (Filter.Eventually.of_forall hCψ)) (fun q => by ring)
    rw [← hAeqLimit]
    refine (hAconv i).congr' ?_
    filter_upwards [] with n
    exact hAeq i n
  have hBlim (i : Fin 3) :
      Tendsto (fun n => ∫ q : Vec3 × ℝ, uε i n q * (φ q * gε i n q)
        ∂(volume : Measure (Vec3 × ℝ))) atTop
        (𝓝 (∫ q : Vec3 × ℝ, u i q * (φ q * g i q)
          ∂(volume : Measure (Vec3 × ℝ)))) := by
    have hBeqLimit : inner ℝ ((hL2u i).toLp (u i))
        ((memLp_mul_left_of_nnnorm_bound hφmeas (hL2g i)
          (Filter.Eventually.of_forall hCφ)).toLp (fun q => φ q * g i q)) =
        ∫ q : Vec3 × ℝ, u i q * (φ q * g i q)
          ∂(volume : Measure (Vec3 × ℝ)) :=
      inner_real_toLp_eq_integral (hL2u i)
        (memLp_mul_left_of_nnnorm_bound hφmeas (hL2g i)
          (Filter.Eventually.of_forall hCφ)) (fun _ => rfl)
    rw [← hBeqLimit]
    refine (hBconv i).congr' ?_
    filter_upwards [] with n
    exact hBeq i n
  have hlimit (i : Fin 3) :
      (∫ q : Vec3 × ℝ, u i q ^ 2 * ψ q ∂(volume : Measure (Vec3 × ℝ))) =
        -(2 * ∫ q : Vec3 × ℝ, u i q * (φ q * g i q)
          ∂(volume : Measure (Vec3 × ℝ))) := by
    have hAseq := hAlim i
    have heq : (fun n => ∫ q : Vec3 × ℝ, uε i n q ^ 2 * ψ q
        ∂(volume : Measure (Vec3 × ℝ))) = fun n =>
        -(2 * ∫ q : Vec3 × ℝ, uε i n q * (φ q * gε i n q)
          ∂(volume : Measure (Vec3 × ℝ))) := by
      funext n
      exact hcomponent i n
    have hBseq' : Tendsto
        (fun n => -(2 * ∫ q : Vec3 × ℝ, uε i n q * (φ q * gε i n q)
          ∂(volume : Measure (Vec3 × ℝ)))) atTop
        (𝓝 (-(2 * ∫ q : Vec3 × ℝ, u i q * (φ q * g i q)
          ∂(volume : Measure (Vec3 × ℝ))))) := by
      have hscale : Continuous (fun x : ℝ => -(2 * x)) := by continuity
      exact (hscale.tendsto _).comp (hBlim i)
    exact tendsto_nhds_unique (heq ▸ hAseq) hBseq'
  classical
  have hsum : (∑ i : Fin 3,
      ∫ q : Vec3 × ℝ, u i q ^ 2 * ψ q ∂(volume : Measure (Vec3 × ℝ))) =
      -(2 * ∑ i : Fin 3,
        ∫ q : Vec3 × ℝ, u i q * (φ q * g i q)
          ∂(volume : Measure (Vec3 × ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact hlimit i
  simpa [u, g, ψ, w₀, Dtw₀, V, spaceTimeSet, parabolicHomeomorph_symm_apply,
    mul_assoc, mul_comm, mul_left_comm] using hsum

end CKN

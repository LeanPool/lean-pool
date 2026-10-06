/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.SpaceTimeMollifier
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Data
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Local Energy Mollified Momentum

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CKN

local instance localEnergyMollifiedVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

/-- Directional derivatives of space-time mollifications are obtained by differentiating the
kernel under the convolution integral. -/
private theorem spaceTimeMollify_fderiv_integral
    {f : Vec3 × ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : LocallyIntegrable f (volume : Measure (Vec3 × ℝ)))
    (z v : Vec3 × ℝ) :
    (fderiv ℝ (spaceTimeMollify f δ hδ) z) v =
      ∫ t, (fderiv ℝ (spaceTimeMollifier δ hδ) t) v * f (z - t)
        ∂(volume : Measure (Vec3 × ℝ)) := by
  have hfd := (spaceTimeMollifier_hasCompactSupport hδ).hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (spaceTimeMollifier_contDiff hδ (n := 1)) hf z
  have hfd' : fderiv ℝ (spaceTimeMollify f δ hδ) z =
      (MeasureTheory.convolution (fderiv ℝ (spaceTimeMollifier δ hδ)) f
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec3 × ℝ))
        (volume : Measure (Vec3 × ℝ))) z := by
    simpa [spaceTimeMollify] using hfd.fderiv
  rw [hfd']
  simp only [MeasureTheory.convolution]
  have hKderiv : HasCompactSupport (fun t : Vec3 × ℝ =>
      fderiv ℝ (spaceTimeMollifier δ hδ) t) :=
    (spaceTimeMollifier_hasCompactSupport hδ).fderiv (𝕜 := ℝ)
  have hderivCont : Continuous (fun t : Vec3 × ℝ =>
      fderiv ℝ (spaceTimeMollifier δ hδ) t) :=
    (spaceTimeMollifier_contDiff hδ (n := 2)).continuous_fderiv (by simp)
  have hconv : ConvolutionExists (fderiv ℝ (spaceTimeMollifier δ hδ)) f
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec3 × ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    exact HasCompactSupport.convolutionExists_left
      (𝕜 := ℝ) (G := Vec3 × ℝ) (E := (Vec3 × ℝ) →L[ℝ] ℝ)
      (E' := ℝ) (F := (Vec3 × ℝ) →L[ℝ] ℝ)
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec3 × ℝ))
      hKderiv hderivCont hf
  rw [ContinuousLinearMap.integral_apply (hconv z) v]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]

/-- The space-time mollifier reflected and translated to the point `z`. -/
@[expose]
def translatedMollifier (z : Vec3 × ℝ) (δ : ℝ) (hδ : 0 < δ) :
    Vec3 × ℝ → ℝ := fun y => spaceTimeMollifier δ hδ (z - y)

/-- A vector test with the translated space-time mollifier in coordinate `i`. -/
@[expose]
def mollifierVectorTest (z : Vec3 × ℝ) (i : Fin 3)
    (δ : ℝ) (hδ : 0 < δ) : Vec3 × ℝ → Vec3 :=
  fun y => Pi.single i (translatedMollifier z δ hδ y)

private theorem translatedMollifier_contDiff (z : Vec3 × ℝ) {δ : ℝ}
    (hδ : 0 < δ) : ContDiff ℝ (⊤ : ℕ∞) (translatedMollifier z δ hδ) := by
  exact (spaceTimeMollifier_contDiff hδ).comp (contDiff_const.sub contDiff_id)

private theorem translatedMollifier_hasCompactSupport (z : Vec3 × ℝ) {δ : ℝ}
    (hδ : 0 < δ) : HasCompactSupport (translatedMollifier z δ hδ) := by
  have hfun : (fun y => spaceTimeMollifier δ hδ (z - y)) =
      spaceTimeMollifier δ hδ ∘ Homeomorph.subLeft z := by
    funext y
    rfl
  change HasCompactSupport (fun y => spaceTimeMollifier δ hδ (z - y))
  rw [hfun]
  exact (spaceTimeMollifier_hasCompactSupport hδ).comp_homeomorph (Homeomorph.subLeft z)

private theorem translatedMollifier_tsupport (z : Vec3 × ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    tsupport (translatedMollifier z δ hδ) = Metric.closedBall z δ := by
  have hcomp : tsupport (translatedMollifier z δ hδ) =
      (Homeomorph.subLeft z) ⁻¹' tsupport (spaceTimeMollifier δ hδ) := by
    have hfun : (fun y => spaceTimeMollifier δ hδ (z - y)) =
        spaceTimeMollifier δ hδ ∘ Homeomorph.subLeft z := by
      funext y
      rfl
    change tsupport (fun y => spaceTimeMollifier δ hδ (z - y)) = _
    rw [hfun]
    exact tsupport_comp_eq_preimage (spaceTimeMollifier δ hδ) (Homeomorph.subLeft z)
  have hkernel : tsupport (spaceTimeMollifier δ hδ) =
      Metric.closedBall (0 : Vec3 × ℝ) δ := by
    simpa [spaceTimeMollifier, spaceTimeStandardBump] using
      (spaceTimeStandardBump δ hδ).tsupport_normed_eq
  rw [hcomp, hkernel]
  ext y
  simp only [Set.mem_preimage, Metric.mem_closedBall]
  rw [dist_eq_norm, dist_eq_norm]
  simp [norm_sub_rev]

private theorem mollifierVectorTest_contDiff (z : Vec3 × ℝ) (i : Fin 3)
    {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifierVectorTest z i δ hδ) := by
  rw [contDiff_pi]
  intro j
  by_cases hji : j = i
  · subst j
    simp only [mollifierVectorTest, translatedMollifier, Pi.single_eq_same]
    exact translatedMollifier_contDiff z hδ
  · simpa [mollifierVectorTest, hji] using
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec3 × ℝ => (0 : ℝ)))

private theorem mollifierVectorTest_hasCompactSupport (z : Vec3 × ℝ)
    (i : Fin 3) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (mollifierVectorTest z i δ hδ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (translatedMollifier_hasCompactSupport z hδ).isCompact
  intro y hy
  have hyScalar : translatedMollifier z δ hδ y ≠ 0 := by
    by_contra hzero
    apply hy
    funext j
    simp [mollifierVectorTest, hzero]
  exact subset_tsupport _ hyScalar

private theorem mollifierVectorTest_tsupport_subset (z : Vec3 × ℝ) (i : Fin 3)
    {δ : ℝ} (hδ : 0 < δ) :
    tsupport (mollifierVectorTest z i δ hδ) ⊆ Metric.closedBall z δ := by
  apply closure_minimal ?_ (Metric.isClosed_closedBall)
  intro y hy
  have hyScalar : translatedMollifier z δ hδ y ≠ 0 := by
    by_contra hzero
    apply hy
    funext j
    simp [mollifierVectorTest, hzero]
  have hyts : y ∈ tsupport (translatedMollifier z δ hδ) := subset_tsupport _ hyScalar
  simpa [translatedMollifier_tsupport z hδ] using hyts

private theorem translatedMollifier_fderiv_apply (z y v : Vec3 × ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    (fderiv ℝ (translatedMollifier z δ hδ) y) v =
      -((fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)) v) := by
  have hk : ContDiff ℝ (⊤ : ℕ∞) (spaceTimeMollifier δ hδ) :=
    spaceTimeMollifier_contDiff hδ
  have hinner : HasFDerivAt (fun q : Vec3 × ℝ => z - q)
      (-(1 : Vec3 × ℝ →L[ℝ] Vec3 × ℝ)) y :=
    (hasFDerivAt_id y).const_sub z
  have houter : HasFDerivAt (spaceTimeMollifier δ hδ)
      (fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)) (z - y) :=
    (hk.differentiable (by simp) (z - y)).hasFDerivAt
  have hcomp := houter.comp y hinner
  have hfd : fderiv ℝ (translatedMollifier z δ hδ) y =
      (fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)).comp
        (-(1 : Vec3 × ℝ →L[ℝ] Vec3 × ℝ)) := by
    change fderiv ℝ (fun q => spaceTimeMollifier δ hδ (z - q)) y = _
    simpa only [Function.comp_def] using hcomp.fderiv
  rw [hfd]
  simp [ContinuousLinearMap.comp_apply]

private theorem integrable_mul_translatedMollifier_fderiv
    {f : Vec3 × ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : LocallyIntegrable f (volume : Measure (Vec3 × ℝ)))
    (z v : Vec3 × ℝ) :
    Integrable (fun y => f y * (fderiv ℝ (translatedMollifier z δ hδ) y) v)
      (volume : Measure (Vec3 × ℝ)) := by
  have hkernelSmooth := translatedMollifier_contDiff z hδ
  have hderivCont : Continuous (fun y : Vec3 × ℝ =>
      (fderiv ℝ (translatedMollifier z δ hδ) y) v) := by
    exact (hkernelSmooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hderivCompact : HasCompactSupport (fun y : Vec3 × ℝ =>
      (fderiv ℝ (translatedMollifier z δ hδ) y) v) :=
    (translatedMollifier_hasCompactSupport z hδ).fderiv_apply (𝕜 := ℝ) v
  have h := hf.integrable_smul_right_of_hasCompactSupport hderivCont hderivCompact
  simpa only [smul_eq_mul] using h

private theorem integral_mul_translatedMollifier_fderiv_eq_neg
    {f : Vec3 × ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : LocallyIntegrable f (volume : Measure (Vec3 × ℝ)))
    (z v : Vec3 × ℝ) :
    ∫ y, f y * (fderiv ℝ (translatedMollifier z δ hδ) y) v
      ∂(volume : Measure (Vec3 × ℝ)) =
      -((fderiv ℝ (spaceTimeMollify f δ hδ) z) v) := by
  have hmul := integrable_mul_translatedMollifier_fderiv hδ hf z v
  have hchange :
      (∫ t, (fderiv ℝ (spaceTimeMollifier δ hδ) t) v * f (z - t)
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ y, (fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)) v * f y
        ∂(volume : Measure (Vec3 × ℝ)) := by
    let H : Vec3 × ℝ → ℝ := fun y =>
      (fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)) v * f y
    calc
      _ = ∫ t, H (z - t) ∂(volume : Measure (Vec3 × ℝ)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        simp [H, sub_sub_cancel]
      _ = ∫ y, H y ∂(volume : Measure (Vec3 × ℝ)) :=
        (Measure.measurePreserving_sub_left (volume : Measure (Vec3 × ℝ)) z).integral_comp
          (Homeomorph.subLeft z).measurableEmbedding H
      _ = _ := rfl
  calc
    (∫ y, f y * (fderiv ℝ (translatedMollifier z δ hδ) y) v
        ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ y, ((fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)) v) * f y
          ∂(volume : Measure (Vec3 × ℝ)) := by
            rw [show (fun y => f y * (fderiv ℝ (translatedMollifier z δ hδ) y) v) =
                fun y => -(((fderiv ℝ (spaceTimeMollifier δ hδ) (z - y)) v) * f y) by
              funext y
              rw [translatedMollifier_fderiv_apply z y v hδ]
              ring]
            rw [integral_neg]
    _ = -((fderiv ℝ (spaceTimeMollify f δ hδ) z) v) := by
      rw [← hchange, ← spaceTimeMollify_fderiv_integral hδ hf z v]

/-- The unit direction in the time coordinate of product spacetime. -/
@[expose]
def energyTimeDir : Vec3 × ℝ := (0, 1)

/-- The unit direction in the `j`th spatial coordinate of product spacetime. -/
@[expose]
def energySpatialDir (j : Fin 3) : Vec3 × ℝ := (basisVec j, 0)

/-- The derivative of a scalar spacetime function in a fixed direction. -/
@[expose]
def energyDirDeriv (f : Vec3 × ℝ → ℝ) (v z : Vec3 × ℝ) : ℝ :=
  (fderiv ℝ f z) v

/-- The weak momentum integrand used to pass the local equation through a mollifier. -/
@[expose]
def mollifiedMomentumWeakIntegrand
    (u : Vec3 × ℝ → Vec3) (F G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (p : Vec3 × ℝ → ℝ) (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) : ℝ :=
  -(∑ i : Fin 3, u z i * energyDirDeriv (fun y => φ y i) energyTimeDir z)
    - ∑ i : Fin 3, ∑ j : Fin 3,
        F z i j * energyDirDeriv (fun y => φ y i) (energySpatialDir j) z
    + ∑ i : Fin 3, ∑ j : Fin 3,
        G z i j * energyDirDeriv (fun y => φ y i) (energySpatialDir j) z
    - p z * ∑ i : Fin 3,
        energyDirDeriv (fun y => φ y i) (energySpatialDir i) z

/-- A distributional momentum identity convolved by the space-time kernel gives the smooth
momentum equation in every ball on which the kernel stays inside the testing domain. -/
theorem spaceTimeMollify_momentum_fderiv_of_weak
    {U : Set (Vec3 × ℝ)}
    {u : Vec3 × ℝ → Vec3} {F G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {p : Vec3 × ℝ → ℝ}
    (hweak : ∀ φ : Vec3 × ℝ → Vec3,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, mollifiedMomentumWeakIntegrand u F G p φ z
        ∂(volume : Measure (Vec3 × ℝ)) = 0)
    (hu : ∀ i, LocallyIntegrable (fun z => u z i)
      (volume : Measure (Vec3 × ℝ)))
    (hF : ∀ i j, LocallyIntegrable (fun z => F z i j)
      (volume : Measure (Vec3 × ℝ)))
    (hG : ∀ i j, LocallyIntegrable (fun z => G z i j)
      (volume : Measure (Vec3 × ℝ)))
    (hp : LocallyIntegrable p (volume : Measure (Vec3 × ℝ)))
    {δ : ℝ} (hδ : 0 < δ) {z : Vec3 × ℝ}
    (hz : Metric.closedBall z δ ⊆ U) :
    ∀ i : Fin 3,
      (fderiv ℝ (spaceTimeMollify (fun y => u y i) δ hδ) z) energyTimeDir
        + ∑ j : Fin 3,
            (fderiv ℝ (spaceTimeMollify (fun y => F y i j) δ hδ) z)
              (energySpatialDir j)
        - ∑ j : Fin 3,
            (fderiv ℝ (spaceTimeMollify (fun y => G y i j) δ hδ) z)
              (energySpatialDir j)
        + (fderiv ℝ (spaceTimeMollify p δ hδ) z) (energySpatialDir i) = 0 := by
  intro i
  let φ := mollifierVectorTest z i δ hδ
  have hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    change ContDiff ℝ (⊤ : ℕ∞) (mollifierVectorTest z i δ hδ)
    exact mollifierVectorTest_contDiff z i hδ
  have hφcompact : HasCompactSupport φ := by
    change HasCompactSupport (mollifierVectorTest z i δ hδ)
    exact mollifierVectorTest_hasCompactSupport z i hδ
  have hφsupport : tsupport φ ⊆ U := by
    change tsupport (mollifierVectorTest z i δ hδ) ⊆ U
    exact (mollifierVectorTest_tsupport_subset z i hδ).trans hz
  have htested := hweak φ hφsmooth hφcompact hφsupport
  have hcomponent (k : Fin 3) :
      (fun y => φ y k) =
        if k = i then translatedMollifier z δ hδ else fun _ => 0 := by
    funext y
    by_cases hki : k = i
    · subst k
      simp [φ, mollifierVectorTest]
    · simp [φ, mollifierVectorTest, hki]
  have htestDeriv (k : Fin 3) (v y : Vec3 × ℝ) :
      energyDirDeriv (fun q => φ q k) v y =
        if k = i then energyDirDeriv (translatedMollifier z δ hδ) v y else 0 := by
    rw [hcomponent k]
    by_cases hki : k = i
    · simp [hki, energyDirDeriv]
    · simp [hki, energyDirDeriv]
  have htested' :
      ∫ y, -(u y i * energyDirDeriv (translatedMollifier z δ hδ)
              energyTimeDir y)
          - ∑ j : Fin 3, F y i j * energyDirDeriv
              (translatedMollifier z δ hδ) (energySpatialDir j) y
          + ∑ j : Fin 3, G y i j * energyDirDeriv
              (translatedMollifier z δ hδ) (energySpatialDir j) y
          - p y * energyDirDeriv (translatedMollifier z δ hδ)
              (energySpatialDir i) y
        ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    convert htested using 1
    apply integral_congr_ae
    filter_upwards [] with y
    simp [mollifiedMomentumWeakIntegrand, φ, htestDeriv]
  have huInt := integrable_mul_translatedMollifier_fderiv hδ (hu i) z energyTimeDir
  have hpInt := integrable_mul_translatedMollifier_fderiv hδ hp z (energySpatialDir i)
  have hFInt (j : Fin 3) :=
    integrable_mul_translatedMollifier_fderiv hδ (hF i j) z (energySpatialDir j)
  have hGInt (j : Fin 3) :=
    integrable_mul_translatedMollifier_fderiv hδ (hG i j) z (energySpatialDir j)
  have hFsumInt : Integrable
      (fun y => ∑ j : Fin 3, F y i j *
        energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y)
      (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum
    intro j hj
    exact hFInt j
  have hGsumInt : Integrable
      (fun y => ∑ j : Fin 3, G y i j *
        energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y)
      (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum
    intro j hj
    exact hGInt j
  have hNegUInt : Integrable
      (fun y => -(u y i * energyDirDeriv (translatedMollifier z δ hδ) energyTimeDir y))
      (volume : Measure (Vec3 × ℝ)) := huInt.neg
  have hNegUSubFInt : Integrable
      (fun y => -(u y i * energyDirDeriv (translatedMollifier z δ hδ) energyTimeDir y)
        - ∑ j : Fin 3, F y i j *
          energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y)
      (volume : Measure (Vec3 × ℝ)) := hNegUInt.sub hFsumInt
  have hPlusGInt : Integrable
      (fun y => (-(u y i * energyDirDeriv (translatedMollifier z δ hδ) energyTimeDir y)
        - ∑ j : Fin 3, F y i j *
          energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y)
        + ∑ j : Fin 3, G y i j *
          energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y)
      (volume : Measure (Vec3 × ℝ)) := hNegUSubFInt.add hGsumInt
  have hWholeInt : Integrable
      (fun y => (-(u y i * energyDirDeriv (translatedMollifier z δ hδ) energyTimeDir y)
        - ∑ j : Fin 3, F y i j *
          energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y)
        + ∑ j : Fin 3, G y i j *
          energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y
        - p y * energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir i) y)
      (volume : Measure (Vec3 × ℝ)) := hPlusGInt.sub hpInt
  have hdecomp :
      (∫ y, -(u y i * energyDirDeriv (translatedMollifier z δ hδ) energyTimeDir y)
          - ∑ j : Fin 3, F y i j *
            energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y
          + ∑ j : Fin 3, G y i j *
            energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y
          - p y * energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir i) y
        ∂(volume : Measure (Vec3 × ℝ))) =
        -(∫ y, u y i * energyDirDeriv (translatedMollifier z δ hδ)
            energyTimeDir y ∂(volume : Measure (Vec3 × ℝ)))
          - (∫ y, ∑ j : Fin 3, F y i j *
              energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y
            ∂(volume : Measure (Vec3 × ℝ)))
          + (∫ y, ∑ j : Fin 3, G y i j *
              energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y
            ∂(volume : Measure (Vec3 × ℝ)))
          - (∫ y, p y * energyDirDeriv (translatedMollifier z δ hδ)
              (energySpatialDir i) y ∂(volume : Measure (Vec3 × ℝ))) := by
    simp only [energyDirDeriv] at hpInt hFInt hGInt hFsumInt hGsumInt
    simp only [energyDirDeriv] at hNegUInt hNegUSubFInt hPlusGInt
    simp only [energyDirDeriv]
    rw [integral_sub hPlusGInt hpInt,
      integral_add hNegUSubFInt hGsumInt,
      integral_sub hNegUInt hFsumInt,
      integral_neg,
      integral_finsetSum Finset.univ (fun j hj => hFInt j),
      integral_finsetSum Finset.univ (fun j hj => hGInt j)]
  have hFconv :
      (∑ j : Fin 3, ∫ y, F y i j *
        energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y
        ∂(volume : Measure (Vec3 × ℝ))) =
      -∑ j : Fin 3,
        (fderiv ℝ (spaceTimeMollify (fun y => F y i j) δ hδ) z)
          (energySpatialDir j) := by
    calc
      _ = ∑ j : Fin 3,
          -((fderiv ℝ (spaceTimeMollify (fun y => F y i j) δ hδ) z)
            (energySpatialDir j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact integral_mul_translatedMollifier_fderiv_eq_neg hδ (hF i j) z
                (energySpatialDir j)
      _ = _ := by simp
  have hGconv :
      (∑ j : Fin 3, ∫ y, G y i j *
        energyDirDeriv (translatedMollifier z δ hδ) (energySpatialDir j) y
        ∂(volume : Measure (Vec3 × ℝ))) =
      -∑ j : Fin 3,
        (fderiv ℝ (spaceTimeMollify (fun y => G y i j) δ hδ) z)
          (energySpatialDir j) := by
    calc
      _ = ∑ j : Fin 3,
          -((fderiv ℝ (spaceTimeMollify (fun y => G y i j) δ hδ) z)
            (energySpatialDir j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact integral_mul_translatedMollifier_fderiv_eq_neg hδ (hG i j) z
                (energySpatialDir j)
      _ = _ := by simp
  have htestedDecomp := hdecomp ▸ htested'
  simp only [energyDirDeriv] at htestedDecomp hFconv hGconv
  rw [integral_finsetSum Finset.univ (fun j hj => hFInt j),
    integral_finsetSum Finset.univ (fun j hj => hGInt j)] at htestedDecomp
  rw [integral_mul_translatedMollifier_fderiv_eq_neg hδ (hu i) z energyTimeDir,
    hFconv, hGconv,
    integral_mul_translatedMollifier_fderiv_eq_neg hδ hp z (energySpatialDir i)]
    at htestedDecomp
  linear_combination htestedDecomp

/-- A weakly divergence-free locally integrable velocity remains divergence free after local
space-time mollification. -/
theorem spaceTimeMollify_divergence_eq_zero_of_weak
    {U : Set (Vec3 × ℝ)} {u : Vec3 × ℝ → Vec3}
    (hweak : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      ∫ z, ∑ i : Fin 3, u z i *
        (fderiv ℝ ψ z) (energySpatialDir i)
        ∂(volume : Measure (Vec3 × ℝ)) = 0)
    (hu : ∀ i, LocallyIntegrable (fun z => u z i)
      (volume : Measure (Vec3 × ℝ)))
    {δ : ℝ} (hδ : 0 < δ) {z : Vec3 × ℝ}
    (hz : Metric.closedBall z δ ⊆ U) :
    ∑ i : Fin 3,
      (fderiv ℝ (spaceTimeMollify (fun y => u y i) δ hδ) z)
        (energySpatialDir i) = 0 := by
  let ψ := translatedMollifier z δ hδ
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := translatedMollifier_contDiff z hδ
  have hψc : HasCompactSupport ψ := translatedMollifier_hasCompactSupport z hδ
  have hψsupport : tsupport ψ ⊆ U := by
    rw [translatedMollifier_tsupport z hδ]
    exact hz
  have htested := hweak ψ hψ hψc hψsupport
  have hInt (i : Fin 3) : Integrable
      (fun y => u y i * (fderiv ℝ ψ y) (energySpatialDir i))
      (volume : Measure (Vec3 × ℝ)) :=
    integrable_mul_translatedMollifier_fderiv hδ (hu i) z (energySpatialDir i)
  have hsumInt : Integrable
      (fun y => ∑ i : Fin 3, u y i * (fderiv ℝ ψ y) (energySpatialDir i))
      (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum
    intro i hi
    exact hInt i
  have hsum :
      (∫ y, ∑ i : Fin 3, u y i * (fderiv ℝ ψ y) (energySpatialDir i)
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∑ i : Fin 3, ∫ y, u y i * (fderiv ℝ ψ y) (energySpatialDir i)
        ∂(volume : Measure (Vec3 × ℝ)) := by
    exact integral_finsetSum Finset.univ (fun i hi => hInt i)
  have hconv (i : Fin 3) :
      (∫ y, u y i * (fderiv ℝ ψ y) (energySpatialDir i)
        ∂(volume : Measure (Vec3 × ℝ))) =
      -((fderiv ℝ (spaceTimeMollify (fun y => u y i) δ hδ) z)
        (energySpatialDir i)) := by
    exact integral_mul_translatedMollifier_fderiv_eq_neg hδ (hu i) z
      (energySpatialDir i)
  calc
    _ = -∑ i : Fin 3, ∫ y, u y i * (fderiv ℝ ψ y) (energySpatialDir i)
          ∂(volume : Measure (Vec3 × ℝ)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        simpa using (congrArg Neg.neg (hconv i)).symm
    _ = -(∫ y, ∑ i : Fin 3, u y i * (fderiv ℝ ψ y) (energySpatialDir i)
          ∂(volume : Measure (Vec3 × ℝ))) := by rw [hsum]
    _ = 0 := by rw [htested]; simp

end CKN

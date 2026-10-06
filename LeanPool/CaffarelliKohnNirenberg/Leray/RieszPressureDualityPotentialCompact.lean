/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityLp
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Compact potential tests for pressure duality

The spatial distribution identity is transported through the space-time
operator for smooth, compactly supported tests.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The spatial coordinate derivative written on the space-time carrier,
used by `lem:riesz-duality`. -/
@[expose]
def rieszPressureJointDirection (f : Vec3 × ℝ → ℝ) (i : Fin 3) :
    Vec3 × ℝ → ℝ := fun z => (fderiv ℝ f z) (CKN.basisVec i, 0)

/-- The spatial Hessian component written on the space-time carrier,
used by `lem:riesz-duality`. -/
@[expose]
def rieszPressureJointHessian (f : Vec3 × ℝ → ℝ) (i j : Fin 3) :
    Vec3 × ℝ → ℝ :=
  rieszPressureJointDirection (rieszPressureJointDirection f j) i

/-- The spatial Laplacian written on the space-time carrier, used by
`lem:riesz-duality`. -/
@[expose]
def rieszPressureJointLaplacian (f : Vec3 × ℝ → ℝ) : Vec3 × ℝ → ℝ :=
  fun z => ∑ i : Fin 3, rieszPressureJointHessian f i i z

/-- A spatial slice derivative agrees with the joint directional derivative,
used by `lem:riesz-duality`. -/
theorem rieszPressure_sliceSpatialDeriv_eq_joint
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialDeriv (fun x : Vec3 => f (x, z.2)) i z.1 =
      rieszPressureJointDirection f i z := by
  let e : Vec3 → Vec3 × ℝ := fun x => (x, z.2)
  have he : HasFDerivAt e (ContinuousLinearMap.inl ℝ Vec3 ℝ) z.1 :=
    hasFDerivAt_prodMk_left z.1 z.2
  have hcomp := (hf.differentiable (by norm_num) z).hasFDerivAt.comp z.1 he
  have hderiv : fderiv ℝ (fun x : Vec3 => f (x, z.2)) z.1 =
      (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ) := by
    change fderiv ℝ (f ∘ e) z.1 = _
    exact hcomp.fderiv
  change (fderiv ℝ (fun x : Vec3 => f (x, z.2)) z.1) (CKN.basisVec i) = _
  rw [hderiv]
  simp [rieszPressureJointDirection, ContinuousLinearMap.inl_apply]

/-- A spatial slice Hessian agrees with the joint spatial Hessian, used by
`lem:riesz-duality`. -/
theorem rieszPressure_sliceMixedSecond_eq_joint
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    CKN.mixedSecond (fun x : Vec3 => f (x, z.2)) i j z.1 =
      rieszPressureJointHessian f i j z := by
  let g : Vec3 × ℝ → ℝ := rieszPressureJointDirection f j
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    dsimp [g, rieszPressureJointDirection]
    have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
      (contDiff_infty_iff_fderiv.mp hf).2
    exact hfd.clm_apply (contDiff_const :
      ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec3 × ℝ => (CKN.basisVec j, (0 : ℝ))))
  have hinner : CKN.spatialDeriv (fun x : Vec3 => f (x, z.2)) j =
      fun x => g (x, z.2) := by
    funext x
    exact rieszPressure_sliceSpatialDeriv_eq_joint hf j (x, z.2)
  rw [CKN.mixedSecond, hinner]
  exact rieszPressure_sliceSpatialDeriv_eq_joint hg i z

/-- A spatial slice Laplacian agrees with the joint spatial Laplacian,
used by `lem:riesz-duality`. -/
theorem rieszPressure_sliceLaplacian_eq_joint
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : Vec3 × ℝ) :
    CKN.spatialLaplacian (fun x : Vec3 => f (x, z.2)) z.1 =
      rieszPressureJointLaplacian f z := by
  simp only [CKN.spatialLaplacian, rieszPressureJointLaplacian,
    rieszPressureJointHessian]
  apply Finset.sum_congr rfl
  intro i hi
  exact rieszPressure_sliceMixedSecond_eq_joint hf i i z

/-- Spatial directional derivatives preserve smoothness, used by
`lem:riesz-duality`. -/
theorem rieszPressureJointDirection_contDiff
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (rieszPressureJointDirection f i) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2
  exact hfd.clm_apply (contDiff_const :
    ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec3 × ℝ => (CKN.basisVec i, (0 : ℝ))))

/-- Spatial Hessian components preserve smoothness, used by
`lem:riesz-duality`. -/
theorem rieszPressureJointHessian_contDiff
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (rieszPressureJointHessian f i j) :=
  rieszPressureJointDirection_contDiff
    (rieszPressureJointDirection_contDiff hf j) i

/-- Spatial Hessians of compactly supported functions have compact support,
used by `lem:riesz-duality`. -/
theorem rieszPressureJointHessian_hasCompactSupport
    {f : Vec3 × ℝ → ℝ} (hfc : HasCompactSupport f) (i j : Fin 3) :
    HasCompactSupport (rieszPressureJointHessian f i j) := by
  have hfirst : HasCompactSupport (rieszPressureJointDirection f j) := by
    change HasCompactSupport (fun z => (fderiv ℝ f z) (CKN.basisVec j, (0 : ℝ)))
    exact hfc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j, (0 : ℝ))
  change HasCompactSupport
    (fun z => (fderiv ℝ (rieszPressureJointDirection f j) z) (CKN.basisVec i, (0 : ℝ)))
  exact hfirst.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i, (0 : ℝ))

/-- Spatial Laplacians of compactly supported functions have compact support,
used by `lem:riesz-duality`. -/
theorem rieszPressureJointLaplacian_hasCompactSupport
    {f : Vec3 × ℝ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (rieszPressureJointLaplacian f) := by
  apply HasCompactSupport.of_support_subset_isCompact hfc.isCompact
  intro z hz
  change rieszPressureJointLaplacian f z ≠ 0 at hz
  by_contra hnot
  have hz0 : z ∉ tsupport f := hnot
  have hderiv0 (i : Fin 3) : rieszPressureJointHessian f i i z = 0 := by
    have hdir : z ∉ tsupport (rieszPressureJointDirection f i) := by
      intro hmem
      apply hz0
      exact (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := f) (CKN.basisVec i, (0 : ℝ))) hmem
    dsimp [rieszPressureJointHessian, rieszPressureJointDirection]
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hdir]
    simp
  simp [rieszPressureJointLaplacian, hderiv0] at hz

/-- The spatial Laplacian preserves smoothness, used by
`lem:riesz-duality`. -/
theorem rieszPressureJointLaplacian_contDiff
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
  ContDiff ℝ (⊤ : ℕ∞) (rieszPressureJointLaplacian f) := by
  unfold rieszPressureJointLaplacian
  exact ContDiff.sum (s := Finset.univ) fun i hi => rieszPressureJointHessian_contDiff hf i i

/-- A compact smooth potential test satisfies the component distributional
identity, used by `lem:riesz-duality`. -/
theorem rieszPressureComponentCompactClass_laplacian_pairing
    (r : ℝ) (hr : 1 < r) (q : ℝ)
    (hHolder : r.HolderConjugate q) (i j : Fin 3)
    {F ψ : Vec3 × ℝ → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ z, (rieszPressureComponentCompactClass r hr i j (F := F) hF hFc :
        Vec3 × ℝ → ℝ) z * rieszPressureJointLaplacian ψ z =
      -∫ z, F z * rieszPressureJointHessian ψ i j z := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have : (ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal q) :=
    Real.HolderConjugate.ennrealOfReal hHolder
  have hLapC : Continuous (rieszPressureJointLaplacian ψ) :=
    (rieszPressureJointLaplacian_contDiff hψ).continuous
  have hLapCpt : HasCompactSupport (rieszPressureJointLaplacian ψ) :=
    rieszPressureJointLaplacian_hasCompactSupport hψc
  have hHessC : Continuous (rieszPressureJointHessian ψ i j) :=
    (rieszPressureJointHessian_contDiff hψ i j).continuous
  have hHessCpt : HasCompactSupport (rieszPressureJointHessian ψ i j) :=
    rieszPressureJointHessian_hasCompactSupport hψc i j
  have hLapMem : MemLp (rieszPressureJointLaplacian ψ) (ENNReal.ofReal q)
      (volume : Measure (Vec3 × ℝ)) := hLapC.memLp_of_hasCompactSupport hLapCpt
  have hHessMem : MemLp (rieszPressureJointHessian ψ i j) (ENNReal.ofReal q)
      (volume : Measure (Vec3 × ℝ)) := hHessC.memLp_of_hasCompactSupport hHessCpt
  have hFMem : MemLp F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    hF.memLp_of_hasCompactSupport hFc
  let P := rieszPressureComponentCompactClass r hr i j (F := F) hF hFc
  obtain ⟨Pfun, hPmeas, hPmem, hPclass, hPslice⟩ :=
    exists_rieszPressureComponentCompactClass_representative r hr i j hF hFc
  have hPLap : Integrable (fun z : Vec3 × ℝ => Pfun z *
      rieszPressureJointLaplacian ψ z) ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
    exact (hPmem.integrable_mul hLapMem)
  have hFHess : Integrable (fun z : Vec3 × ℝ => F z *
      rieszPressureJointHessian ψ i j z) ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
    exact hFMem.integrable_mul hHessMem
  have hSections : ∀ᵐ t ∂(volume : Measure ℝ),
      ∫ x, Pfun (x, t) * rieszPressureJointLaplacian ψ (x, t) =
        -∫ x, F (x, t) * rieszPressureJointHessian ψ i j (x, t) := by
    filter_upwards [hPslice] with t hPt
    let f : Vec3 → ℝ := fun x => F (x, t)
    let ψt : Vec3 → ℝ := fun x => ψ (x, t)
    have hf : Continuous f := hF.comp (continuous_id.prodMk continuous_const)
    have hfc : HasCompactSupport f := continuous_spaceTimeSlice_hasCompactSupport hFc t
    have hψt : ContDiff ℝ (⊤ : ℕ∞) ψt := by
      exact hψ.comp (contDiff_id.prodMk contDiff_const)
    have hψtc : HasCompactSupport ψt := continuous_spaceTimeSlice_hasCompactSupport hψc t
    have hfr : MemLp f (ENNReal.ofReal r) (volume : Measure Vec3) :=
      hf.memLp_of_hasCompactSupport hfc
    have hf2 : MemLp f 2 (volume : Measure Vec3) :=
      hf.memLp_of_hasCompactSupport hfc
    have hsp := rieszPressureOperator_laplacian_pairing r hr i j f hfr hf2 ψt hψt hψtc
    calc
      ∫ x, Pfun (x, t) * rieszPressureJointLaplacian ψ (x, t) =
          ∫ x, rieszPressureOperator r hr i j (hfr.toLp f) x *
            CKN.spatialLaplacian ψt x := by
              apply integral_congr_ae
              filter_upwards [hPt] with x hx
              rw [hx, rieszPressure_sliceLaplacian_eq_joint hψ (x, t)]
      _ = -∫ x, f x * CKN.mixedSecond ψt i j x := hsp
      _ = -∫ x, F (x, t) * rieszPressureJointHessian ψ i j (x, t) := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with x
            rw [rieszPressure_sliceMixedSecond_eq_joint hψ i j (x, t)]
  calc
    ∫ z, (P : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) z *
        rieszPressureJointLaplacian ψ z =
        ∫ z, Pfun z * rieszPressureJointLaplacian ψ z := by
          apply integral_congr_ae
          filter_upwards [hPclass] with z hz
          exact congrArg (fun y : ℝ => y * rieszPressureJointLaplacian ψ z) hz.symm
    _ = ∫ t, ∫ x, Pfun (x, t) * rieszPressureJointLaplacian ψ (x, t) := by
          rw [Measure.volume_eq_prod]
          exact integral_prod_symm _ hPLap
    _ = ∫ t, -(∫ x, F (x, t) * rieszPressureJointHessian ψ i j (x, t)) := by
          apply integral_congr_ae
          exact hSections
    _ = -∫ t, ∫ x, F (x, t) * rieszPressureJointHessian ψ i j (x, t) := by
          rw [integral_neg]
    _ = -∫ z, F z * rieszPressureJointHessian ψ i j z := by
          rw [Measure.volume_eq_prod]
          congr 1
          exact (integral_prod_symm _ hFHess).symm

end CKN.Leray

end

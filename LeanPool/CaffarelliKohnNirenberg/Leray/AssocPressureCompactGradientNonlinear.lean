/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureCompactGradientCore

/-!
# Nonlinear gradient cancellation

Cancellation of the convection and pressure terms on compact scalar gradient tests.
-/

public section

open MeasureTheory Set Filter
open Filter
open scoped ENNReal
open scoped Convolution
open scoped Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section

namespace CKN.Leray

/-- The nonlinear and pressure terms cancel on a compact smooth gradient test,
by the proved noncompact Riesz duality identity. -/
theorem associatedPressureCompactGradient_nonlinearPressure_cancel
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ (Set.univ : Set Vec3) ×ˢ Ioo 0 T) :
    ∫ z : Vec3 × ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3,
        u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
          CKN.spatialSecondPartialProd g i j z) +
        rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
          (associatedPressureTensor T u)
          (associatedPressureTensor_memLp_threeHalves hLH) z *
          rieszPressureJointLaplacian g z
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  let Q : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioo 0 T
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let F := associatedPressureTensor T u
  let hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := fun i j =>
    associatedPressureTensor_memLp_threeHalves hLH i j
  let p3 := rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF
  have hQmeas : MeasurableSet Q := by
    dsimp [Q]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hμ : μ = (volume : Measure (Vec3 × ℝ)).restrict Q := by
    calc
      μ = ((volume : Measure Vec3).restrict Set.univ).prod
          (volume.restrict (Ioo 0 T)) := by simp [μ]
      _ = ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict Q := by
        rw [Measure.prod_restrict]
      _ = (volume : Measure (Vec3 × ℝ)).restrict Q := by
        rw [← Measure.volume_eq_prod Vec3 ℝ]
  have hdecay := associatedPressurePotentialDecay_of_compactSupport hg hgc
  have hDual := rieszPressureSpaceTime_noncompactPotential_duality
    F hF hg hdecay
  have hLapSmooth : ContDiff ℝ (⊤ : ℕ∞) (rieszPressureJointLaplacian g) :=
    rieszPressureJointLaplacian_contDiff hg
  have hLapCompact : HasCompactSupport (rieszPressureJointLaplacian g) := by
    have hzero : ∀ z ∉ tsupport g,
        rieszPressureJointLaplacian g z = 0 := by
      intro z hz
      unfold rieszPressureJointLaplacian
      apply Finset.sum_eq_zero
      intro i hi
      rw [← rieszPressure_sliceMixedSecond_eq_joint hg i i z]
      exact CKN.spatialSecondPartial_eq_zero_off_tsupport hz i i
    exact HasCompactSupport.intro hgc.isCompact (by
      intro z hz
      exact hzero z hz)
  have hLapMem : MemLp (rieszPressureJointLaplacian g)
      (ENNReal.ofReal (3 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    hLapSmooth.continuous.memLp_of_hasCompactSupport hLapCompact
  have hPMem : MemLp p3 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    dsimp [p3, F, hF]
    exact rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num)
      (associatedPressureTensor T u)
      (fun i j => associatedPressureTensor_memLp_threeHalves hLH i j)
  have hLapMu : MemLp (rieszPressureJointLaplacian g)
      (ENNReal.ofReal (3 : ℝ)) μ := by
    rw [hμ]
    exact hLapMem.restrict Q
  have hPMu : MemLp p3 (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    rw [hμ]
    exact hPMem.restrict Q
  have hFmu (i j : Fin 3) : MemLp (F i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    rw [hμ]
    exact (hF i j).restrict Q
  have hHessSmooth (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (rieszPressureJointHessian g i j) :=
    rieszPressureJointHessian_contDiff hg i j
  have hHessCompact (i j : Fin 3) :
      HasCompactSupport (rieszPressureJointHessian g i j) :=
    rieszPressureJointHessian_hasCompactSupport hgc i j
  have hHessMem (i j : Fin 3) : MemLp (rieszPressureJointHessian g i j)
      (ENNReal.ofReal (3 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    (hHessSmooth i j).continuous.memLp_of_hasCompactSupport (hHessCompact i j)
  have hHessMu (i j : Fin 3) : MemLp (rieszPressureJointHessian g i j)
      (ENNReal.ofReal (3 : ℝ)) μ := by
    rw [hμ]
    exact (hHessMem i j).restrict Q
  let : ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ))
      (ENNReal.ofReal (3 : ℝ)) 1 := by
    have h : Real.HolderTriple (3 / 2 : ℝ) 3 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hFInt (i j : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      F i j z * rieszPressureJointHessian g i j z) μ :=
    (hFmu i j).integrable_mul (hHessMu i j)
  have hConvAE (i j : Fin 3) :
      (fun z : Vec3 × ℝ =>
        u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
          CKN.spatialSecondPartialProd g i j z) =ᵐ[μ]
      fun z => F i j z * rieszPressureJointHessian g i j z := by
    rw [hμ]
    filter_upwards [ae_restrict_mem hQmeas] with z hz
    have htime : z.2 ∈ Ioo 0 T := by simpa [Q] using hz
    have hzQ : z ∈ Q := by
      exact ⟨Set.mem_univ _, htime⟩
    have hmem : parabolicHomeomorph.symm z ∈
        spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
      change ((z.1, z.2) : ParabolicPoint) ∈
        (Set.univ : Set Vec3) ×ˢ Ioo 0 T
      exact ⟨Set.mem_univ _, htime⟩
    have hsecond : CKN.spatialSecondPartialProd g i j z =
        rieszPressureJointHessian g i j z := by
      change CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) j i z.1 = _
      have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, z.2)) :=
        hg.comp (contDiff_prodMk_left (𝕜 := ℝ)
          (n := (⊤ : ℕ∞)) z.2)
      calc
        CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) j i z.1 =
            CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) i j z.1 :=
          CKN.mixedSecond_swap hslice j i z.1
        _ = rieszPressureJointHessian g i j z :=
          rieszPressure_sliceMixedSecond_eq_joint hg i j z
    have hpre : z ∈ parabolicHomeomorph.symm ⁻¹'
        spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := hmem
    simp [associatedPressureTensor, F, hpre, hsecond]
  have hConvInt (i j : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
        CKN.spatialSecondPartialProd g i j z) μ :=
    (hFInt i j).congr (hConvAE i j).symm
  have hPressInt : Integrable (fun z : Vec3 × ℝ =>
      p3 z * rieszPressureJointLaplacian g z) μ := hPMu.integrable_mul hLapMu
  have hconvSumInt : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
          CKN.spatialSecondPartialProd g i j z) μ := by
    apply integrable_finsetSum (s := Finset.univ)
    intro i hi
    apply integrable_finsetSum (s := Finset.univ)
    intro j hj
    exact hConvInt i j
  have hconvSum : ∫ z : Vec3 × ℝ,
      ∑ i : Fin 3, ∑ j : Fin 3,
        u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
          CKN.spatialSecondPartialProd g i j z ∂μ =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            CKN.spatialSecondPartialProd g i j z ∂μ := by
    rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => hConvInt i j))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum _ (fun j hj => hConvInt i j)]
  have hconvTerm (i j : Fin 3) :
      ∫ z : Vec3 × ℝ,
        u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
          CKN.spatialSecondPartialProd g i j z ∂μ =
        ∫ z : Vec3 × ℝ, F i j z *
          rieszPressureJointHessian g i j z ∂(volume : Measure (Vec3 × ℝ)) := by
    rw [hμ]
    calc
        ∫ z in Q,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            CKN.spatialSecondPartialProd g i j z ∂(volume : Measure (Vec3 × ℝ)) =
        ∫ z in Q, F i j z * rieszPressureJointHessian g i j z ∂volume := by
          apply setIntegral_congr_ae hQmeas
          filter_upwards [] with z hz
          have htime : z.2 ∈ Ioo 0 T := by simpa [Q] using hz
          have hzQ : z ∈ Q := ⟨Set.mem_univ _, htime⟩
          have hmem : parabolicHomeomorph.symm z ∈
              spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
            change ((z.1, z.2) : ParabolicPoint) ∈
              (Set.univ : Set Vec3) ×ˢ Ioo 0 T
            exact ⟨Set.mem_univ _, htime⟩
          have hsecond : CKN.spatialSecondPartialProd g i j z =
              rieszPressureJointHessian g i j z := by
            change CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) j i z.1 = _
            have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, z.2)) :=
              hg.comp (contDiff_prodMk_left (𝕜 := ℝ)
                (n := (⊤ : ℕ∞)) z.2)
            calc
              CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) j i z.1 =
                  CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) i j z.1 :=
                CKN.mixedSecond_swap hslice j i z.1
              _ = rieszPressureJointHessian g i j z :=
                rieszPressure_sliceMixedSecond_eq_joint hg i j z
          have hpre : z ∈ parabolicHomeomorph.symm ⁻¹'
              spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := hmem
          simp [associatedPressureTensor, F, hpre, hsecond]
      _ = ∫ z, F i j z * rieszPressureJointHessian g i j z ∂volume := by
        rw [← integral_indicator hQmeas]
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ Q
        · simp [hz]
        · have hnot : parabolicHomeomorph.symm z ∉
              spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
            have hnotTime : z.2 ∉ Ioo 0 T := by simpa [Q] using hz
            change ¬ (((z.1, z.2) : ParabolicPoint) ∈
              (Set.univ : Set Vec3) ×ˢ Ioo 0 T)
            intro hmem
            exact hnotTime hmem.2
          have hpre : z ∉ parabolicHomeomorph.symm ⁻¹'
              spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := hnot
          simp [associatedPressureTensor, F, hpre]
  have hpressGlobal :
      ∫ z : Vec3 × ℝ, p3 z * rieszPressureJointLaplacian g z
          ∂(volume : Measure (Vec3 × ℝ)) =
      ∫ z : Vec3 × ℝ, p3 z * rieszPressureJointLaplacian g z ∂μ := by
    calc
      ∫ z, p3 z * rieszPressureJointLaplacian g z ∂volume =
        ∫ z in Q, p3 z * rieszPressureJointLaplacian g z ∂volume := by
          calc
            _ = ∫ z, Q.indicator (fun z => p3 z *
                rieszPressureJointLaplacian g z) z ∂volume := by
                  apply integral_congr_ae
                  filter_upwards [] with z
                  by_cases hz : z ∈ Q
                  · simp [hz]
                  · have hnot : z ∉ tsupport g := fun hm => hz (hgsupp hm)
                    have hzero : rieszPressureJointLaplacian g z = 0 := by
                      unfold rieszPressureJointLaplacian
                      apply Finset.sum_eq_zero
                      intro i hi
                      rw [← rieszPressure_sliceMixedSecond_eq_joint hg i i z]
                      exact CKN.spatialSecondPartial_eq_zero_off_tsupport hnot i i
                    simp [hz, hzero]
            _ = _ := integral_indicator hQmeas
      _ = ∫ z : Vec3 × ℝ, p3 z * rieszPressureJointLaplacian g z ∂μ := by
          rw [← hμ]
  calc
    ∫ z : Vec3 × ℝ,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            CKN.spatialSecondPartialProd g i j z) +
          p3 z * rieszPressureJointLaplacian g z ∂μ =
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            CKN.spatialSecondPartialProd g i j z ∂μ) +
        ∫ z : Vec3 × ℝ, p3 z * rieszPressureJointLaplacian g z ∂μ := by
          rw [integral_add hconvSumInt hPressInt, hconvSum]
    _ = (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ, F i j z * rieszPressureJointHessian g i j z
          ∂(volume : Measure (Vec3 × ℝ))) +
        ∫ z : Vec3 × ℝ, p3 z * rieszPressureJointLaplacian g z
          ∂(volume : Measure (Vec3 × ℝ)) := by
          rw [hpressGlobal]
          apply congrArg₂ HAdd.hAdd
          · apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            exact hconvTerm i j
          · rfl
    _ = 0 := by
      rw [hDual]
      ring

/-- The complete Leray momentum functional vanishes on the gradient of a
compact smooth scalar potential, for the canonical associated pressure. -/
theorem associatedPressureCompactGradient_momentum_zero
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ (Set.univ : Set Vec3) ×ˢ Ioo 0 T) :
    ∫ z : Vec3 × ℝ,
      (-(∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
          CKN.timePartialProd (CKN.spatialPartialProd g i) z))
        - (∑ i : Fin 3, ∑ j : Fin 3,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            CKN.spatialSecondPartialProd g i j z)
        + (∑ i : Fin 3, ∑ j : Fin 3,
          Du (parabolicHomeomorph.symm z) i j *
            CKN.spatialSecondPartialProd g i j z)
        - rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
            (associatedPressureTensor T u)
            (associatedPressureTensor_memLp_fiveThirds hLH) z *
            rieszPressureJointLaplacian g z
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  let Q : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioo 0 T
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let F := associatedPressureTensor T u
  let hF5 := associatedPressureTensor_memLp_fiveThirds hLH
  let hF3 := associatedPressureTensor_memLp_threeHalves hLH
  let p5 := rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num) F hF5
  let p3 := rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF3
  let N : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
        CKN.spatialSecondPartialProd g i j z
  let V : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      Du (parabolicHomeomorph.symm z) i j *
        CKN.spatialSecondPartialProd g i j z
  let W : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3,
      u (parabolicHomeomorph.symm z) i *
        CKN.timePartialProd (CKN.spatialPartialProd g i) z
  have hQmeas : MeasurableSet Q := by
    dsimp [Q]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hμ : μ = (volume : Measure (Vec3 × ℝ)).restrict Q := by
    calc
      μ = ((volume : Measure Vec3).restrict Set.univ).prod
          (volume.restrict (Ioo 0 T)) := by simp [μ]
      _ = ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict Q := by
        rw [Measure.prod_restrict]
      _ = (volume : Measure (Vec3 × ℝ)).restrict Q := by
        rw [← Measure.volume_eq_prod Vec3 ℝ]
  have hU : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2 μ := by
    simpa [μ] using associatedPressureSolution_velocity_memLp_two_productSlab hLH
  have hDu : MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) 2 μ := by
    simpa [μ] using associatedPressureSolution_gradient_memLp_two_productSlab hLH
  have hLapSmooth : ContDiff ℝ (⊤ : ℕ∞) (rieszPressureJointLaplacian g) :=
    rieszPressureJointLaplacian_contDiff hg
  have hLapCompact : HasCompactSupport (rieszPressureJointLaplacian g) := by
    have hzero : ∀ z ∉ tsupport g,
        rieszPressureJointLaplacian g z = 0 := by
      intro z hz
      unfold rieszPressureJointLaplacian
      apply Finset.sum_eq_zero
      intro i hi
      rw [← rieszPressure_sliceMixedSecond_eq_joint hg i i z]
      exact CKN.spatialSecondPartial_eq_zero_off_tsupport hz i i
    exact HasCompactSupport.intro hgc.isCompact (by
      intro z hz
      exact hzero z hz)
  have hLap2 : MemLp (rieszPressureJointLaplacian g) 2 μ := by
    have hglobal : MemLp (rieszPressureJointLaplacian g) 2
        (volume : Measure (Vec3 × ℝ)) :=
      hLapSmooth.continuous.memLp_of_hasCompactSupport hLapCompact
    rw [hμ]
    exact hglobal.restrict Q
  have hLap3 : MemLp (rieszPressureJointLaplacian g)
      (ENNReal.ofReal (3 : ℝ)) μ := by
    have hglobal : MemLp (rieszPressureJointLaplacian g)
        (ENNReal.ofReal (3 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
      hLapSmooth.continuous.memLp_of_hasCompactSupport hLapCompact
    rw [hμ]
    exact hglobal.restrict Q
  have hHsmooth (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialSecondPartialProd g i j) := by
    exact CKN.spatialPartial_contDiff (CKN.spatialPartial_contDiff hg i) j
  have hHcompact (i j : Fin 3) :
      HasCompactSupport (CKN.spatialSecondPartialProd g i j) := by
    change HasCompactSupport (fun z : Vec3 × ℝ =>
      CKN.spatialSecondPartial (show ParabolicPoint → ℝ from g) i j
        (z.1, z.2))
    exact CKN.hasCompactSupport_spatialPartial
      (CKN.hasCompactSupport_spatialPartial hgc i) j
  have hH2 (i j : Fin 3) : MemLp (CKN.spatialSecondPartialProd g i j) 2 μ := by
    simpa [μ] using associatedPressureCompact_memLp_two (T := T)
      (hHsmooth i j) (hHcompact i j)
  have hH3 (i j : Fin 3) : MemLp (CKN.spatialSecondPartialProd g i j)
      (ENNReal.ofReal (3 : ℝ)) μ := by
    have hglobal : MemLp (CKN.spatialSecondPartialProd g i j)
        (ENNReal.ofReal (3 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
      (hHsmooth i j).continuous.memLp_of_hasCompactSupport (hHcompact i j)
    rw [hμ]
    exact hglobal.restrict Q
  have hTimeSmooth (i : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞)
        (CKN.timePartialProd (CKN.spatialPartialProd g i)) := by
    exact CKN.contDiff_timePartial (CKN.spatialPartial_contDiff hg i)
  have hTimeCompact (i : Fin 3) :
      HasCompactSupport (CKN.timePartialProd (CKN.spatialPartialProd g i)) := by
    exact CKN.hasCompactSupport_timePartial
      (CKN.hasCompactSupport_spatialPartial hgc i)
  have hTime2 (i : Fin 3) :
      MemLp (CKN.timePartialProd (CKN.spatialPartialProd g i)) 2 μ := by
    simpa [μ] using associatedPressureCompact_memLp_two (T := T)
      (hTimeSmooth i) (hTimeCompact i)
  have : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have : ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ))
      (ENNReal.ofReal (3 : ℝ)) 1 := by
    have h : Real.HolderTriple (3 / 2 : ℝ) 3 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hWterm (i : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm z) i *
        CKN.timePartialProd (CKN.spatialPartialProd g i) z) μ := by
    have hUi : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i) 2 μ :=
      (memLp_pi_iff.mp hU) i
    have hprod : MemLp (fun z : Vec3 × ℝ =>
        u (parabolicHomeomorph.symm z) i *
          CKN.timePartialProd (CKN.spatialPartialProd g i) z) 1 μ :=
      hUi.mul (hTime2 i)
    exact memLp_one_iff_integrable.mp hprod
  have hVterm (i j : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      Du (parabolicHomeomorph.symm z) i j *
        CKN.spatialSecondPartialProd g i j z) μ := by
    have hDuij : MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z) i j) 2 μ :=
      (memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j
    have hprod : MemLp (fun z : Vec3 × ℝ =>
        Du (parabolicHomeomorph.symm z) i j *
          CKN.spatialSecondPartialProd g i j z) 1 μ :=
      hDuij.mul (hH2 i j)
    exact memLp_one_iff_integrable.mp hprod
  have hFmu (i j : Fin 3) : MemLp (F i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    rw [hμ]
    exact (associatedPressureTensor_memLp_threeHalves hLH i j).restrict Q
  have hNconv (i j : Fin 3) :
      (fun z : Vec3 × ℝ =>
        u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
          CKN.spatialSecondPartialProd g i j z) =ᵐ[μ]
      fun z => F i j z * CKN.spatialSecondPartialProd g i j z := by
    rw [hμ]
    filter_upwards [ae_restrict_mem hQmeas] with z hz
    have htime : z.2 ∈ Ioo 0 T := by simpa [Q] using hz
    have hmem : parabolicHomeomorph.symm z ∈
        spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
      change ((z.1, z.2) : ParabolicPoint) ∈
        (Set.univ : Set Vec3) ×ˢ Ioo 0 T
      exact ⟨Set.mem_univ _, htime⟩
    have hpre : z ∈ parabolicHomeomorph.symm ⁻¹'
        spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := hmem
    simp [associatedPressureTensor, F, hpre]
  have hNterm (i j : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
        CKN.spatialSecondPartialProd g i j z) μ := by
    have hbase : Integrable (fun z : Vec3 × ℝ =>
        F i j z * CKN.spatialSecondPartialProd g i j z) μ :=
      (hFmu i j).integrable_mul (hH3 i j)
    exact Integrable.congr hbase (hNconv i j).symm
  have hP3 : MemLp p3 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    dsimp [p3, F, hF3]
    exact rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num)
      (associatedPressureTensor T u)
      (fun i j => associatedPressureTensor_memLp_threeHalves hLH i j)
  have hP3mu : MemLp p3 (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    rw [hμ]
    exact hP3.restrict Q
  have hLapInt : Integrable (fun z : Vec3 × ℝ =>
      p3 z * rieszPressureJointLaplacian g z) μ := hP3mu.integrable_mul hLap3
  have hPae := associatedPressureForSolution_rieszPressureThreeHalves_ae_eq hLH
  have hPae' : p5 =ᵐ[volume] p3 := by
    simpa [p5, p3, F, hF5, hF3] using hPae
  have hPaeMu : p5 =ᵐ[μ] p3 := by
    rw [hμ]
    exact ae_restrict_of_ae (s := Q) hPae'
  have hP5Int : Integrable (fun z : Vec3 × ℝ =>
      p5 z * rieszPressureJointLaplacian g z) μ := by
    apply Integrable.congr hLapInt
    filter_upwards [hPaeMu] with z hz
    simp [hz]
  have hWint : Integrable W μ := by
    dsimp [W]
    apply integrable_finsetSum
    intro i hi
    exact hWterm i
  have hVint : Integrable V μ := by
    dsimp [V]
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact hVterm i j
  have hNint : Integrable N μ := by
    dsimp [N]
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact hNterm i j
  have hWzero := associatedPressureCompactGradient_timeTerm_zero hLH hg hgc
  have hVzero := associatedPressureCompactGradient_viscosity_cancel hLH hg hgc
  have hNPzero := associatedPressureCompactGradient_nonlinearPressure_cancel
    hLH hg hgc hgsupp
  have hPIntegrals :
      ∫ z : Vec3 × ℝ, p5 z * rieszPressureJointLaplacian g z ∂μ =
        ∫ z : Vec3 × ℝ, p3 z * rieszPressureJointLaplacian g z ∂μ := by
    apply integral_congr_ae
    filter_upwards [hPaeMu] with z hz
    simp [hz]
  have hNPlusP3 :
      ∫ z : Vec3 × ℝ, N z +
        p3 z * rieszPressureJointLaplacian g z ∂μ = 0 := by
    simpa [N, p3, F, hF3] using hNPzero
  have hWzero' : ∫ z : Vec3 × ℝ, W z ∂μ = 0 := by
    simpa [W] using hWzero
  have hVzero' : ∫ z : Vec3 × ℝ, V z ∂μ = 0 := by
    simpa [V] using hVzero
  have hNPlusP5 :
      ∫ z : Vec3 × ℝ, N z +
        p5 z * rieszPressureJointLaplacian g z ∂μ = 0 := by
    calc
      _ = ∫ z : Vec3 × ℝ, N z +
          p3 z * rieszPressureJointLaplacian g z ∂μ := by
        rw [integral_add hNint hP5Int, integral_add hNint hLapInt,
          hPIntegrals]
      _ = 0 := hNPlusP3
  have hpoint :
      (fun z : Vec3 × ℝ =>
        (-(∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
            CKN.timePartialProd (CKN.spatialPartialProd g i) z))
          - (∑ i : Fin 3, ∑ j : Fin 3,
            u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
              CKN.spatialSecondPartialProd g i j z)
          + (∑ i : Fin 3, ∑ j : Fin 3,
            Du (parabolicHomeomorph.symm z) i j *
              CKN.spatialSecondPartialProd g i j z)
          - p5 z * rieszPressureJointLaplacian g z) =
      (fun z : Vec3 × ℝ =>
        -W z - (N z + p5 z * rieszPressureJointLaplacian g z) + V z) := by
    funext z
    simp only [W, N, V]
    ring
  have hAddSplit :
      ∫ z : Vec3 × ℝ,
          -W z - (N z + p5 z * rieszPressureJointLaplacian g z) + V z ∂μ =
        (∫ z : Vec3 × ℝ, -W z -
            (N z + p5 z * rieszPressureJointLaplacian g z) ∂μ) +
          ∫ z : Vec3 × ℝ, V z ∂μ := by
    simpa using integral_add
      (hWint.neg.sub (hNint.add hP5Int)) hVint
  have hSubSplit :
      ∫ z : Vec3 × ℝ,
          -W z - (N z + p5 z * rieszPressureJointLaplacian g z) ∂μ =
        (∫ z : Vec3 × ℝ, -W z ∂μ) -
          ∫ z : Vec3 × ℝ,
            N z + p5 z * rieszPressureJointLaplacian g z ∂μ := by
    simpa using integral_sub hWint.neg (hNint.add hP5Int)
  calc
    ∫ z : Vec3 × ℝ,
        (-(∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
            CKN.timePartialProd (CKN.spatialPartialProd g i) z))
          - (∑ i : Fin 3, ∑ j : Fin 3,
            u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
              CKN.spatialSecondPartialProd g i j z)
          + (∑ i : Fin 3, ∑ j : Fin 3,
            Du (parabolicHomeomorph.symm z) i j *
              CKN.spatialSecondPartialProd g i j z)
          - p5 z * rieszPressureJointLaplacian g z ∂μ =
      ∫ z : Vec3 × ℝ,
        -W z - (N z + p5 z * rieszPressureJointLaplacian g z) + V z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact congrFun hpoint z
    _ = (-(∫ z : Vec3 × ℝ, W z ∂μ) -
          ∫ z : Vec3 × ℝ,
            N z + p5 z * rieszPressureJointLaplacian g z ∂μ) +
          ∫ z : Vec3 × ℝ, V z ∂μ := by
      rw [hAddSplit, hSubSplit, integral_neg]
    _ = 0 := by rw [hWzero', hNPlusP5, hVzero']; ring

end CKN.Leray

end

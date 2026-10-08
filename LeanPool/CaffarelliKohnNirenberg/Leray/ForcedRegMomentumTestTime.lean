/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumTest

/-!
# Space-time tests in frequency variables

A smooth compactly supported space-time vector test has, at every time, a
Schwartz slice; its spatial transform is jointly continuous in frequency and
time, differentiable in time with the transform of the time derivative as
derivative, turns spatial derivatives into multiplication by `2πiξⱼ`, and is
square integrable in frequency and time. These are the test transforms in the
frequency form of `eq:reg-momentum-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace LineDeriv

noncomputable section

namespace CKN.Leray

/-- The spatial partial derivative of a space-time field. -/
@[expose]
def spaceDeriv (j : Fin 3) (φ : Vec3 × ℝ → Vec3) : Vec3 × ℝ → Vec3 :=
  fun z => fderiv ℝ φ z (CKN.basisVec j, 0)

/-- The time derivative of a space-time field. -/
@[expose]
def timeDeriv (φ : Vec3 × ℝ → Vec3) : Vec3 × ℝ → Vec3 :=
  fun z => fderiv ℝ φ z (0, 1)

section Smooth

variable {φ : Vec3 × ℝ → Vec3}

theorem contDiff_fderiv_apply (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v : Vec3 × ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ φ z v) :=
  (hφ.fderiv_right (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_fderiv_apply (hφc : HasCompactSupport φ) (v : Vec3 × ℝ) :
    HasCompactSupport (fun z => fderiv ℝ φ z v) :=
  (hφc.fderiv ℝ).comp_left (g := fun L : Vec3 × ℝ →L[ℝ] Vec3 => L v) (by simp)

theorem contDiff_spaceDeriv (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (spaceDeriv j φ) := contDiff_fderiv_apply hφ _

theorem hasCompactSupport_spaceDeriv (hφc : HasCompactSupport φ) (j : Fin 3) :
    HasCompactSupport (spaceDeriv j φ) := hasCompactSupport_fderiv_apply hφc _

theorem contDiff_timeDeriv (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (timeDeriv φ) := contDiff_fderiv_apply hφ _

theorem hasCompactSupport_timeDeriv (hφc : HasCompactSupport φ) :
    HasCompactSupport (timeDeriv φ) := hasCompactSupport_fderiv_apply hφc _

theorem contDiff_slice (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ (x, t)) :=
  hφ.comp (contDiff_id.prodMk contDiff_const)

theorem hasCompactSupport_slice (hφc : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (fun x => φ (x, t)) := by
  refine HasCompactSupport.intro (hφc.image continuous_fst) fun x hx => ?_
  exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨(x, t), h, rfl⟩

theorem hasFDerivAt_slice (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec3) (t : ℝ) :
    HasFDerivAt (fun y => φ (y, t))
      ((fderiv ℝ φ (x, t)).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ)) x :=
  ((hφ.differentiable (by simp)) (x, t)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)

theorem hasDerivAt_time_slice (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec3) (t : ℝ) :
    HasDerivAt (fun s => φ (x, s)) (timeDeriv φ (x, t)) t := by
  have h := ((hφ.differentiable (by simp)) (x, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  exact h

/-- The CKN spatial partial derivative of a component is the component of the
spatial partial derivative. -/
theorem spatialPartial_eq_spaceDeriv (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i j : Fin 3)
    (z : Vec3 × ℝ) :
    CKN.spatialPartial (fun y => φ y i) j z = spaceDeriv j φ z i := by
  unfold CKN.spatialPartial spaceDeriv
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp z.1
    (hasFDerivAt_slice hφ z.1 z.2)
  have h' : HasFDerivAt (fun y : Vec3 => φ (y, z.2) i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
        ((fderiv ℝ φ (z.1, z.2)).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ))) z.1 := h
  rw [h'.fderiv]
  rfl

/-- The CKN time partial derivative of a component is the component of the
time derivative. -/
theorem timePartial_eq_timeDeriv (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.timePartial (fun y => φ y i) z = timeDeriv φ z i := by
  unfold CKN.timePartial
  have h' : HasFDerivAt (fun s : ℝ => φ (z.1, s) i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (timeDeriv φ (z.1, z.2)))) z.2 :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp z.2
      (hasDerivAt_time_slice hφ z.1 z.2).hasFDerivAt
  rw [h'.fderiv]
  simp

end Smooth

/-- The spatial transform of the time slices of a space-time test. -/
@[expose]
def testHat (φ : Vec3 × ℝ → Vec3) (p : L2Vec3 × ℝ) : ComplexVec3 :=
  𝓕 (testField (fun x => φ (x, p.2))) p.1

theorem testHat_eq_integral (φ : Vec3 × ℝ → Vec3) (p : L2Vec3 × ℝ) :
    testHat φ p = ∫ y, 𝐞 (-⟪y, p.1⟫) • testField (fun x => φ (x, p.2)) y :=
  Real.fourier_eq _ _

theorem testHat_eq_zero {φ : Vec3 × ℝ → Vec3} {t : ℝ} (h : ∀ x, φ (x, t) = 0) (ξ : L2Vec3) :
    testHat φ (ξ, t) = 0 := by
  rw [testHat_eq_integral]
  simp [testField, h]

section Transform

variable {φ : Vec3 × ℝ → Vec3}

/-- The slices of a smooth compactly supported test are dominated by one
square-integrable function. -/
theorem exists_testField_bound (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∃ b : L2Vec3 → ℝ, Integrable b ∧ Integrable (fun y => b y ^ 2) ∧
      ∀ t y, ‖testField (fun x => φ (x, t)) y‖ ≤ b y := by
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support
    (coordComplexify.continuous.comp hφ.continuous) (hφc.comp_left (map_zero coordComplexify))
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  let K : Set L2Vec3 := e '' (Prod.fst '' tsupport φ)
  have hK : IsCompact K := (hφc.image continuous_fst).image e.continuous
  refine ⟨K.indicator fun _ => M, ?_, ?_, fun t y => ?_⟩
  · exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  · have h : (fun y => K.indicator (fun _ => M) y ^ 2) = K.indicator fun _ => M ^ 2 := by
      funext y
      by_cases hy : y ∈ K
      · simp [indicator_of_mem hy]
      · simp [indicator_of_notMem hy]
    rw [h]
    exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  · by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
      exact hM _
    · rw [indicator_of_notMem hy]
      have hz : φ (WithLp.ofLp y, t) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun h => hy ?_
        exact ⟨WithLp.ofLp y, ⟨(WithLp.ofLp y, t), h, rfl⟩, rfl⟩
      simp [testField, hz]

theorem continuous_testHat (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Continuous (testHat φ) := by
  obtain ⟨b, hb, -, hbd⟩ := exists_testField_bound hφ hφc
  have heq : testHat φ = fun p : L2Vec3 × ℝ =>
      ∫ y, 𝐞 (-⟪y, p.1⟫) • testField (fun x => φ (x, p.2)) y :=
    funext (testHat_eq_integral φ)
  rw [heq]
  have hcf : Continuous fun q : L2Vec3 × ℝ => coordComplexify (φ (WithLp.ofLp q.1, q.2)) :=
    coordComplexify.continuous.comp (hφ.continuous.comp
      (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous.comp
        continuous_fst).prodMk continuous_snd))
  refine continuous_of_dominated (bound := b) (fun p => ?_)
    (fun p => Eventually.of_forall fun y => ?_) hb (Eventually.of_forall fun y => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    simp only [Circle.smul_def]
    refine (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).neg)).smul ?_
    exact hcf.comp (continuous_id.prodMk continuous_const)
  · rw [Circle.norm_smul]
    exact hbd p.2 y
  · simp only [Circle.smul_def]
    refine (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_inner.comp (continuous_const.prodMk continuous_fst)).neg)).smul ?_
    exact hcf.comp (continuous_const.prodMk continuous_snd)

/-- The transform of a test is differentiable in time, with the transform of
the time derivative as derivative. -/
theorem hasDerivAt_testHat (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (ξ : L2Vec3) (t : ℝ) :
    HasDerivAt (fun s => testHat φ (ξ, s)) (testHat (timeDeriv φ) (ξ, t)) t := by
  obtain ⟨b, hb, -, hbd⟩ := exists_testField_bound hφ hφc
  obtain ⟨b', hb', -, hbd'⟩ := exists_testField_bound (contDiff_timeDeriv hφ)
    (hasCompactSupport_timeDeriv hφc)
  simp only [testHat_eq_integral]
  have hmeas : ∀ (g : Vec3 × ℝ → Vec3), Continuous g → ∀ s : ℝ, AEStronglyMeasurable
      (fun y : L2Vec3 => 𝐞 (-⟪y, ξ⟫) • testField (fun x => g (x, s)) y) volume := by
    intro g hg s
    refine Continuous.aestronglyMeasurable ?_
    simp only [Circle.smul_def]
    refine (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).neg)).smul ?_
    exact coordComplexify.continuous.comp (hg.comp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous.prodMk continuous_const))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) (bound := b')
    (F := fun s y => 𝐞 (-⟪y, ξ⟫) • testField (fun x => φ (x, s)) y)
    (F' := fun s y => 𝐞 (-⟪y, ξ⟫) • testField (fun x => timeDeriv φ (x, s)) y)
    univ_mem (Eventually.of_forall fun s => hmeas φ hφ.continuous s) ?_
    (hmeas _ (contDiff_timeDeriv hφ).continuous t) ?_ hb' ?_).2
  · refine Integrable.mono' hb (hmeas φ hφ.continuous t) (Eventually.of_forall fun y => ?_)
    rw [Circle.norm_smul]
    exact hbd t y
  · exact Eventually.of_forall fun y s _ => by
      rw [Circle.norm_smul]
      exact hbd' s y
  · refine Eventually.of_forall fun y s _ => ?_
    simp only [Circle.smul_def]
    have h := (coordComplexify.hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_time_slice hφ (WithLp.ofLp y) s)).const_smul
        ((𝐞 (-⟪y, ξ⟫) : Circle) : ℂ)
    exact h

/-- The transform turns a spatial derivative into multiplication by `2πiξⱼ`. -/
theorem testHat_spaceDeriv (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (j : Fin 3) (p : L2Vec3 × ℝ) :
    testHat (spaceDeriv j φ) p =
      ((2 * Real.pi * Complex.I) * ((p.1 j : ℝ) : ℂ)) • testHat φ p := by
  set f := testSchwartz (fun x => φ (x, p.2)) (contDiff_slice hφ p.2)
    (hasCompactSupport_slice hφc p.2) with hf
  set m : L2Vec3 := WithLp.toLp 2 (CKN.basisVec j) with hm
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hS : ∂_{m} f = testSchwartz (fun x => spaceDeriv j φ (x, p.2))
      (contDiff_slice (contDiff_spaceDeriv hφ j) p.2)
      (hasCompactSupport_slice (hasCompactSupport_spaceDeriv hφc j) p.2) := by
    refine SchwartzMap.ext fun y => ?_
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, testSchwartz_apply]
    have hd : HasFDerivAt (fun y : L2Vec3 => coordComplexify (φ (WithLp.ofLp y, p.2)))
        (coordComplexify.comp (((fderiv ℝ φ (WithLp.ofLp y, p.2)).comp
          (ContinuousLinearMap.inl ℝ Vec3 ℝ)).comp e.toContinuousLinearMap)) y :=
      coordComplexify.hasFDerivAt.comp y
        ((hasFDerivAt_slice hφ (WithLp.ofLp y) p.2).comp y e.hasFDerivAt)
    change fderiv ℝ (fun y : L2Vec3 => coordComplexify (φ (WithLp.ofLp y, p.2))) y m = _
    rw [hd.fderiv]
    rfl
  have hg : Function.HasTemperateGrowth fun x : L2Vec3 => inner ℝ x m := by fun_prop
  unfold testHat
  rw [← fourier_testSchwartz _ (contDiff_slice (contDiff_spaceDeriv hφ j) p.2)
    (hasCompactSupport_slice (hasCompactSupport_spaceDeriv hφc j) p.2), ← hS,
    SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, hm, inner_toLp_basisVec, hf,
    fourier_testSchwartz, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  rfl

/-- The transform of a test is square integrable in frequency and time. -/
theorem integrable_testHat_sq (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (T : ℝ) :
    Integrable (fun p => ‖testHat φ p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 T))) := by
  obtain ⟨b, -, hb2, hbd⟩ := exists_testField_bound hφ hφc
  let S : ℝ → 𝓢(L2Vec3, ComplexVec3) := fun t => testSchwartz (fun x => φ (x, t))
    (contDiff_slice hφ t) (hasCompactSupport_slice hφc t)
  refine integrable_sq_jointRep_prod (testHat φ) (continuous_testHat hφ hφc).stronglyMeasurable
    (fun t => (𝓕 (S t)).toLp 2) (fun s _ => ?_) (fun _ => ∫ y, b y ^ 2)
    (integrableOn_const (by simp)) (fun s _ => ?_)
  · filter_upwards [(𝓕 (S s)).coeFn_toLp 2 (volume : Measure L2Vec3)] with ξ hξ
    rw [hξ]
    rfl
  · rw [SchwartzMap.norm_fourier_toL2_eq, ← integral_norm_sq_eq_norm_sq_Lp]
    have hae : (fun y => ‖((S s).toLp 2 : L2Vec3 → ComplexVec3) y‖ ^ 2) =ᵐ[volume]
        fun y => ‖testField (fun x => φ (x, s)) y‖ ^ 2 := by
      filter_upwards [(S s).coeFn_toLp 2 (volume : Measure L2Vec3)] with y hy
      rw [hy]
      rfl
    rw [integral_congr_ae hae]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity) hb2
      (Eventually.of_forall fun y => ?_)
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd s y) 2

end Transform

end CKN.Leray

end

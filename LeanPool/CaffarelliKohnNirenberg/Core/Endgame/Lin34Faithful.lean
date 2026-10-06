/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremAAdaptersLin34
public import LeanPool.CaffarelliKohnNirenberg.Pressure.ForceCancellationUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicRemainderForceTerms
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceIntegrated
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredCZResidual
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistribution

/-!
# Lin34Faithful

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
noncomputable section

namespace CKN

/-- The absolute constant controlling both solenoidal clauses of
`prop:lin34`. -/
@[expose]
noncomputable def lin34AbsoluteConstant : ℝ :=
  max (lin34PointwiseConstant lin34CZConstant) (lin34Constant lin34CZConstant)

private theorem lin34AbsoluteConstant_nonneg : 0 ≤ lin34AbsoluteConstant := by
  apply le_trans (lin34PointwiseConstant_nonneg lin34CZConstant_nonneg)
  exact le_max_left _ _

private theorem smoothCompactTest_contDiff_local
    {ψ : Vec3 → ℝ} (hψ : SmoothCompactTest ψ) :
    ContDiff ℝ (⊤ : ℕ∞) ψ :=
  (contDiff_infty).2 hψ.1

private theorem smoothCompactTest_mul_local
    {η ψ : Vec3 → ℝ} (hη : SmoothCompactTest η) (hψ : SmoothCompactTest ψ) :
    SmoothCompactTest (fun x => η x * ψ x) := by
  refine ⟨fun n => ?_, hη.2.mul_right (f' := ψ)⟩
  exact ((smoothCompactTest_contDiff_local hη).mul
    (smoothCompactTest_contDiff_local hψ)).of_le (by simp)

private theorem smoothCompactTest_deriv_integrable_local
    {g ψ : Vec3 → ℝ} (hg : Integrable g volume)
    (hψ : SmoothCompactTest ψ) (i : Fin 3) :
    Integrable (fun x => g x * spatialDeriv ψ i x) volume := by
  have hψtop := smoothCompactTest_contDiff_local hψ
  have hψd := contDiff_spatialDeriv_smooth hψtop i
  have hψdc : HasCompactSupport (spatialDeriv ψ i) :=
    hψ.2.fderiv_apply (𝕜 := ℝ) (basisVec i)
  obtain ⟨C, hC⟩ := hψdc.exists_bound_of_continuous hψd.continuous
  exact hg.mul_bdd hψd.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hC x)

private theorem fderiv_zero_outside_tsupport_local
    {ψ : Vec3 → ℝ} {V : Set Vec3} (hψV : tsupport ψ ⊆ V)
    {x : Vec3} (hx : x ∉ V) : fderiv ℝ ψ x = 0 := by
  have hx' : x ∉ tsupport ψ := fun hmem => hx (hψV hmem)
  have hev : ψ =ᶠ[𝓝 x] (fun _ : Vec3 => (0 : ℝ)) :=
    Filter.eventually_of_mem ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hx')
      (fun y hy => by
        by_contra hne
        exact hy (subset_tsupport ψ (Function.mem_support.mpr hne)))
  rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_const_apply]

private theorem divergence_integral_eq_local
    {V : Set Vec3} {F : Vec3 → Vec3} {ψ : Vec3 → ℝ}
    (hψV : tsupport ψ ⊆ V) :
    ∫ x, ∑ i : Fin 3, F x i * spatialDeriv ψ i x =
      ∫ x in V, ∑ i : Fin 3, F x i * spatialDeriv ψ i x := by
  rw [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    MeasurableSet.univ (subset_univ V)
  intro x hx
  have hxV : x ∉ V := fun hV => hx.2 hV
  apply Finset.sum_eq_zero
  intro i hi
  have hderiv : spatialDeriv ψ i x = 0 := by
    change (fderiv ℝ ψ x) (basisVec i) = 0
    rw [fderiv_zero_outside_tsupport_local hψV hxV]
    simp
  rw [hderiv, mul_zero]

private theorem pressure_force_pairing_zero_on
    {Ω : Set Vec3} {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    (hη : SmoothCompactTest η) (hηΩ : tsupport η ⊆ Ω)
    (hdiv : ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ → tsupport ψ ⊆ Ω →
      ∫ x, ∑ i : Fin 3, f (x, s) i * spatialDeriv ψ i x = 0)
    (hInt7 : ∀ j, Integrable (fun y => η y * f (y, s) j) volume)
    (hSupp7 : ∀ j, HasCompactSupport (fun y => η y * f (y, s) j))
    (hInt8 : ∀ j, Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hSupp8 : ∀ j, HasCompactSupport
      (fun y => spatialDeriv η j y * f (y, s) j)) :
    ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ →
      ∫ x, (pressureP7 η f s x + pressureP8 η f s x) *
        spatialLaplacian ψ x = 0 := by
  intro ψ hψ
  have hηtop := smoothCompactTest_contDiff_local hη
  have hψtop := smoothCompactTest_contDiff_local hψ
  have hηψ := smoothCompactTest_mul_local hη hψ
  have hηψΩ : tsupport (fun x => η x * ψ x) ⊆ Ω := by
    exact (tsupport_mul_subset_left (f := η) (g := ψ)).trans hηΩ
  have hdivηψ := hdiv (fun x => η x * ψ x) hηψ hηψΩ
  have hterm7 (j : Fin 3) : Integrable
      (fun x => η x * f (x, s) j * spatialDeriv ψ j x) volume := by
    exact smoothCompactTest_deriv_integrable_local (hInt7 j) hψ j
  have hterm8 (j : Fin 3) : Integrable
      (fun x => spatialDeriv η j x * f (x, s) j * ψ x) volume := by
    have hψc : HasCompactSupport ψ := hψ.2
    obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψtop.continuous
    exact (hInt8 j).mul_bdd hψtop.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hC x)
  have hsum7 : Integrable
      (fun x => ∑ j : Fin 3, η x * f (x, s) j * spatialDeriv ψ j x) volume :=
    integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _hj => hterm7 j)
  have hsum8 : Integrable
      (fun x => ∑ j : Fin 3, spatialDeriv η j x * f (x, s) j * ψ x) volume :=
    integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _hj => hterm8 j)
  have hdiv' : ∫ x, (∑ j : Fin 3,
      η x * f (x, s) j * spatialDeriv ψ j x) +
        (∑ j : Fin 3, spatialDeriv η j x * f (x, s) j * ψ x) = 0 := by
    calc
      _ = ∫ x, ∑ i : Fin 3, f (x, s) i *
          spatialDeriv (fun y => η y * ψ y) i x := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [show (∑ i : Fin 3, f (x, s) i *
            spatialDeriv (fun y => η y * ψ y) i x) =
          ∑ i : Fin 3, (η x * f (x, s) i * spatialDeriv ψ i x +
            spatialDeriv η i x * f (x, s) i * ψ x) by
          apply Finset.sum_congr rfl
          intro i hi
          rw [spatialDeriv_mul
            (hηtop.differentiable (by simp) x)
            (hψtop.differentiable (by simp) x) i]
          ring]
        rw [← Finset.sum_add_distrib]
      _ = 0 := hdivηψ
  have hdiv'' : (∫ x, ∑ j : Fin 3,
      η x * f (x, s) j * spatialDeriv ψ j x) +
      (∫ x, ∑ j : Fin 3,
        spatialDeriv η j x * f (x, s) j * ψ x) = 0 := by
    calc
      _ = ∫ x, (∑ j : Fin 3,
          η x * f (x, s) j * spatialDeriv ψ j x) +
          (∑ j : Fin 3,
            spatialDeriv η j x * f (x, s) j * ψ x) :=
        (integral_add hsum7 hsum8).symm
      _ = 0 := hdiv'
  have hdivsum : (∑ j : Fin 3, ∫ x,
      η x * f (x, s) j * spatialDeriv ψ j x) +
      (∑ j : Fin 3, ∫ x,
        spatialDeriv η j x * f (x, s) j * ψ x) = 0 := by
    rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))] at hdiv''
    · rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))] at hdiv''
      · exact hdiv''
      · intro j hj
        exact hterm8 j
    · intro j hj
      exact hterm7 j
  have hP7 := pressureP7_distributional_pairing hInt7 hSupp7 hψtop hψ.2
  have hP8 := pressureP8_distributional_pairing hInt8 hSupp8 hψtop hψ.2
  calc
    ∫ x, (pressureP7 η f s x + pressureP8 η f s x) *
        spatialLaplacian ψ x =
      (∫ x, pressureP7 η f s x * spatialLaplacian ψ x) +
        ∫ x, pressureP8 η f s x * spatialLaplacian ψ x := by
      rw [show (fun x => (pressureP7 η f s x + pressureP8 η f s x) *
          spatialLaplacian ψ x) =
        (fun x => pressureP7 η f s x * spatialLaplacian ψ x +
          pressureP8 η f s x * spatialLaplacian ψ x) by
          funext x
          ring]
      have hP7Int : Integrable (fun x => pressureP7 η f s x *
          spatialLaplacian ψ x) volume := by
        have hlocal := pressureP7_locallyIntegrable hInt7 hSupp7
        simpa only [smul_eq_mul, mul_comm] using
          hlocal.integrable_smul_right_of_hasCompactSupport
            (contDiff_spatialLaplacian_smooth hψtop).continuous
            (decomposition_laplacian_hasCompactSupport_sws hψ.2)
      have hP8Int : Integrable (fun x => pressureP8 η f s x *
          spatialLaplacian ψ x) volume := by
        have hlocal := pressureP8_locallyIntegrable hInt8 hSupp8
        simpa only [smul_eq_mul, mul_comm] using
          hlocal.integrable_smul_right_of_hasCompactSupport
            (contDiff_spatialLaplacian_smooth hψtop).continuous
            (decomposition_laplacian_hasCompactSupport_sws hψ.2)
      exact integral_add hP7Int hP8Int
    _ = 0 := by
      rw [hP7, hP8]
      linarith only [hdivsum]

private theorem force_sources_integrable_local
    {f : ParabolicPoint → Vec3} {s : ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) {V : Set Vec3}
    (hfs : Integrable (fun x : Vec3 => f (x, s)) (volume.restrict V))
    (hηV : tsupport (mollifiedBallCutoff x₀ hρ) ⊆ V) :
    (∀ j, Integrable
        (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) volume ∧
      HasCompactSupport
        (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j)) ∧
    (∀ j, Integrable
        (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j) volume ∧
      HasCompactSupport
        (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)) := by
  have hηmeasV : AEStronglyMeasurable (mollifiedBallCutoff x₀ hρ)
      (volume.restrict V) :=
    ((mollifiedBallCutoff_smooth x₀ hρ).continuous.aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hsourceInt (j : Fin 3) : Integrable
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j) volume := by
    have hfc : AEStronglyMeasurable (fun y : Vec3 => f (y, s) j)
        (volume.restrict V) :=
      (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
        hfs.aestronglyMeasurable
    have hfcint : Integrable (fun y : Vec3 => f (y, s) j)
        (volume.restrict V) := by
      simpa only [ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).integrable_comp hfs
    have hmul := hfcint.mul_bdd hηmeasV
      (Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using
          (abs_le.mpr ⟨by linarith only [mollifiedBallCutoff_nonneg x₀ hρ y],
            mollifiedBallCutoff_le_one x₀ hρ y⟩))
    exact decomposition_full_of_on_sws
      (show IntegrableOn
          (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) V volume by
        simpa only [IntegrableOn, mul_comm] using hmul)
      ((tsupport_mul_subset_left (f := mollifiedBallCutoff x₀ hρ)
        (g := fun y => f (y, s) j)).trans hηV)
  have hsourceSupp (j : Fin 3) : HasCompactSupport
      (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) :=
    (mollifiedBallCutoff_hasCompactSupport x₀ hρ).mul_right
  have hderivC (j : Fin 3) : HasCompactSupport
      (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) :=
    (mollifiedBallCutoff_hasCompactSupport x₀ hρ).fderiv_apply
      (𝕜 := ℝ) (basisVec j)
  have hderivV (j : Fin 3) :
      tsupport (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) ⊆ V :=
    (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηV
  have hderivInt (j : Fin 3) : Integrable
      (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j) volume := by
    have hηd := contDiff_spatialDeriv_smooth
      (mollifiedBallCutoff_smooth x₀ hρ) j
    have hηdV : AEStronglyMeasurable
        (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) (volume.restrict V) := by
      have hηdmeas : AEStronglyMeasurable
          (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) volume :=
        hηd.continuous.aestronglyMeasurable
      exact hηdmeas.mono_measure Measure.restrict_le_self
    have hfc : Integrable (fun y : Vec3 => f (y, s) j)
        (volume.restrict V) := by
      simpa only [ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).integrable_comp hfs
    have hmul := hfc.mul_bdd hηdV
      (Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using pressure_cutoff_spatialDeriv_bound x₀ hρ y j)
    exact decomposition_full_of_on_sws
      (show IntegrableOn
          (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j) V volume by
        simpa only [IntegrableOn] using (hmul.congr (Eventually.of_forall fun y => by ring)))
      ((tsupport_mul_subset_left
        (f := spatialDeriv (mollifiedBallCutoff x₀ hρ) j)
        (g := fun y => f (y, s) j)).trans (hderivV j))
  have hderivSupp (j : Fin 3) : HasCompactSupport
      (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j) :=
    (hderivC j).mul_right
  exact ⟨fun j => ⟨hsourceInt j, hsourceSupp j⟩,
    fun j => ⟨hderivInt j, hderivSupp j⟩⟩

private theorem pressure_force_eq_zero_of_localDivergenceFree
    {Ω : Set Vec3} {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    (hη : SmoothCompactTest η) (hηΩ : tsupport η ⊆ Ω)
    (hdiv : ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ → tsupport ψ ⊆ Ω →
      ∫ x, ∑ i : Fin 3, f (x, s) i * spatialDeriv ψ i x = 0)
    (hInt7 : ∀ j, Integrable (fun y => η y * f (y, s) j) volume)
    (hSupp7 : ∀ j, HasCompactSupport (fun y => η y * f (y, s) j))
    (hInt8 : ∀ j, Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hSupp8 : ∀ j, HasCompactSupport
      (fun y => spatialDeriv η j y * f (y, s) j))
    (hmem : ∀ R : ℝ, 0 < R →
      MemLp (pressureP7 η f s + pressureP8 η f s) (ENNReal.ofReal (3 / 2))
        (volume.restrict (euclideanBall (0 : Vec3) R)))
    (hgrowth : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      lpNorm (pressureP7 η f s + pressureP8 η f s) (ENNReal.ofReal (3 / 2))
        (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R)) :
    pressureP7 η f s + pressureP8 η f s =ᵐ[volume] 0 := by
  have hweak : CKN.Foundation.Heat.WeaklyHarmonicOn Set.univ
      (pressureP7 η f s + pressureP8 η f s) := by
    intro ψ hψ hψc _
    have htest : SmoothCompactTest ψ := by
      refine ⟨fun n => ?_, hψc⟩
      exact hψ.of_le (by simp)
    have hzero := pressure_force_pairing_zero_on hη hηΩ hdiv
      hInt7 hSupp7 hInt8 hSupp8 ψ htest
    simpa only [Measure.restrict_univ, Set.mem_univ, true_and, Pi.add_apply] using hzero
  obtain ⟨C, hC, hgrowth'⟩ := hgrowth
  exact CKN.Foundation.Heat.weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth
    hC hmem hweak hgrowth'

/-- For almost every slice of a suitable weak solution, local distributional
divergence on the spatial domain cancels the cutoff force potentials. -/
theorem pressure_force_eq_zero_of_sws_spaceTimeDivergenceFree
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hdiv : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun w => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
          (tsupport ψ) volume ∧
        ∫ w in spaceTimeSet Ω I,
          ∑ i : Fin 3, f w i * spatialPartial ψ i w = 0) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      lin34ForcePart f z.1 ρ hρ s =ᵐ[volume] 0 := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  have hηc : HasCompactSupport η := mollifiedBallCutoff_hasCompactSupport z.1 hρ
  have hηsupport : tsupport η ⊆ vec3Ball z.1 ρ := by
    exact pressure_cutoff_support_subset_ball z.1 hρ
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hηΩ : tsupport η ⊆ Ω := by
    exact hηsupport.trans (fun x hx => hbox.2.2.1 (subset_closure (hball hx)))
  obtain ⟨V, hVopen, hηV, _hVmeas, _hVcompact, hVΩ, hslice⟩ :=
    decomposition_slice_integrability hsol hηc hηΩ hηc hηΩ
  have hTsubI : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I :=
    htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  have hsliceT : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      Integrable (fun x : Vec3 => f (x, s)) (volume.restrict V) := by
    exact (ae_restrict_of_ae_restrict_of_subset hTsubI hslice).mono
      (fun s hs => hs.2.2)
  have hsliceOneTest := divfree_slice_weak hdiv hsol.2.1
  have hsliceDivV : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ V →
      ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
        ∫ x in V, ∑ i : Fin 3, f (x, s) i *
          (fderiv ℝ ψ x) (basisVec i) = 0 := by
    intro ψ hψ hψc hψV'
    have hVsubsetΩ : V ⊆ Ω := subset_closure.trans hVΩ
    have hψΩ : tsupport ψ ⊆ Ω := hψV'.trans hVsubsetΩ
    have htest := hsliceOneTest ψ hψ hψc hψΩ
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hTsubI htest] with s hs
    have hEq : (∫ x in Ω, ∑ i : Fin 3, f (x, s) i *
        (fderiv ℝ ψ x) (basisVec i)) =
        ∫ x in V, ∑ i : Fin 3, f (x, s) i *
          (fderiv ℝ ψ x) (basisVec i) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hsol.1.measurableSet hVsubsetΩ
      intro x hx
      have hxV : x ∉ V := fun hV => hx.2 hV
      apply Finset.sum_eq_zero
      intro i hi
      have hderiv : (fderiv ℝ ψ x) (basisVec i) = 0 := by
        rw [fderiv_zero_outside_tsupport_local hψV' hxV]
        simp
      rw [hderiv, mul_zero]
    exact hEq.symm ▸ hs
  have hloc : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ i : Fin 3, LocallyIntegrableOn (fun x : Vec3 => f (x, s) i) V volume := by
    filter_upwards [hsliceT] with s hs i
    have hi : Integrable (fun x : Vec3 => f (x, s) i)
        (volume.restrict V) := by
      simpa only [ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).integrable_comp hs
    have hiOn : IntegrableOn (fun x : Vec3 => f (x, s) i) V volume := by
      simpa only [IntegrableOn] using hi
    exact hiOn.locallyIntegrableOn
  have hdivV := ae_slice_divergence_zero_of_forall_test hVopen hloc hsliceDivV
  have hproducer := pressure_force_memLp_and_lpNorm_growth_ae_of_sws hsol hρ hsub
  let C : ℝ → ℝ := fun s =>
    CKN.Foundation.Euclidean.pressureP7GrowthConstant η f s
        (vec3EuclideanNorm z.1 + ρ) +
      CKN.Foundation.Euclidean.pressureP8GrowthConstant η f s
        (vec3EuclideanNorm z.1 + ρ)
  have hηtest : SmoothCompactTest η := by
    refine ⟨fun n => ?_, hηc⟩
    exact (mollifiedBallCutoff_smooth z.1 hρ).of_le (by simp)
  filter_upwards [hdivV, hproducer, hsliceT] with s hsdiv hsprod hs
  have hsource := force_sources_integrable_local hρ hs hηV
  have hmem : ∀ R : ℝ, 0 < R →
      MemLp (pressureP7 η f s + pressureP8 η f s) (ENNReal.ofReal (3 / 2))
        (volume.restrict (euclideanBall (0 : Vec3) R)) := hsprod.1
  have hgrowth : ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 0 < R →
      lpNorm (pressureP7 η f s + pressureP8 η f s) (ENNReal.ofReal (3 / 2))
        (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ A * (1 + R) :=
    ⟨C s, hsprod.2.1, hsprod.2.2⟩
  have hηV' : tsupport η ⊆ V := by simpa [η] using hηV
  have hdivGlobal : ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ → tsupport ψ ⊆ V →
      ∫ x, ∑ i : Fin 3, f (x, s) i * spatialDeriv ψ i x = 0 := by
    intro ψ hψ hψV'
    have hlocal := hsdiv ψ (smoothCompactTest_contDiff_local hψ) hψ.2 hψV'
    have hEq := divergence_integral_eq_local (F := fun x => f (x, s)) hψV'
    exact hEq.symm ▸ hlocal
  have hzero := pressure_force_eq_zero_of_localDivergenceFree hηtest hηV'
    hdivGlobal
    (fun j => (hsource.1 j).1) (fun j => (hsource.1 j).2)
    (fun j => (hsource.2 j).1) (fun j => (hsource.2 j).2) hmem hgrowth
  simpa only [lin34ForcePart, η] using hzero

/-- The pointwise estimate of `prop:lin34` follows from local divergence
because the force cutoff is supported inside the spatial domain. -/
theorem lin34_slice_pointwise_bound_ae_of_sws_spaceTimeDivergenceFree
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hdiv : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun w => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
          (tsupport ψ) volume ∧
        ∫ w in spaceTimeSet Ω I,
          ∑ i : Fin 3, f w i * spatialPartial ψ i w = 0) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      r⁻¹ ^ 2 * lin34PressureSlice p z r s ≤
        lin34PointwiseConstant lin34CZConstant *
          ((ρ / r) ^ (2 : ℕ) * lin34G u z ρ s +
            (r / ρ) * lin34H p z ρ s) := by
  have hCZ := lin34_hCZ_p1_of_residual_ae_of_sws hsol hρ hsub
    (lin34_centred_residual_local_growth_ae_of_sws hsol hρ hsub)
  have hbase := lin34_slice_pointwise_bound_ae_of_sws lin34CZConstant
    lin34CZConstant_nonneg hsol hρ hr hhalf hsub hCZ
  have hforce := pressure_force_eq_zero_of_sws_spaceTimeDivergenceFree
    hsol hρ hsub hdiv
  filter_upwards [hbase, hforce] with s hs hf
  have hzero : lin34ForceSliceIntegral f z ρ r hρ s = 0 := by
    have hae : (fun x : Vec3 => |lin34ForcePart f z.1 ρ hρ s x| ^ (3 / 2 : ℝ))
        =ᵐ[volume.restrict (vec3Ball z.1 r)] 0 := by
      filter_upwards [ae_restrict_of_ae hf] with x hx
      simp only [lin34ForcePart, Pi.add_apply, Pi.zero_apply] at hx ⊢
      simp [hx, Real.zero_rpow]
    simpa [lin34ForceSliceIntegral] using integral_eq_zero_of_ae hae
  change r⁻¹ ^ 2 * lin34PressureSlice p z r s ≤
    lin34PointwiseConstant lin34CZConstant *
      ((ρ / r) ^ 2 * lin34G u z ρ s + (r / ρ) * lin34H p z ρ s +
        r⁻¹ ^ 2 * lin34ForceSliceIntegral f z ρ r hρ s) at hs
  rw [hzero, mul_zero, add_zero] at hs
  exact hs

private theorem lin34F_local_nonneg
    {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (s : ℝ) :
    0 ≤ (ρ / r) ^ 2 * lin34G u z ρ s + (r / ρ) * lin34H p z ρ s := by
  have hG : 0 ≤ lin34G u z ρ s := by
    unfold lin34G lin34VelocitySlice
    exact mul_nonneg (by positivity)
      (integral_nonneg fun _ => pow_nonneg (vec3EuclideanNorm_nonneg _) _)
  have hH : 0 ≤ lin34H p z ρ s := by
    unfold lin34H lin34PressureSlice
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)
  exact add_nonneg (mul_nonneg (by positivity) hG) (mul_nonneg (by positivity) hH)

/-- **The three clauses of `prop:lin34`.**  The solenoidal clauses use the
local slice form of `div f = 0` on `Ω`; the final clause is unconditional and
has the `q`-dependent force constant. -/
theorem pressure_lin34_of_sws (q : ℝ) :
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r → r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      (((∀ ψ : Vec3 × ℝ → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
          IntegrableOn (fun w => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
              (tsupport ψ) volume ∧
            ∫ w in spaceTimeSet Ω I,
              ∑ i : Fin 3, f w i * spatialPartial ψ i w = 0) →
          ((∀ᵐ t ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          r⁻¹ ^ 2 * ∫ y in vec3Ball z.1 r, |p (y, t)| ^ (3 / 2 : ℝ) ≤
            lin34AbsoluteConstant *
              ((ρ / r) ^ 2 * (ρ⁻¹ ^ 2 *
                  ∫ y in vec3Ball z.1 ρ,
                    vec3EuclideanNorm (meanFreeVec u z.1 ρ t y) ^ (3 : ℕ)) +
                (r / ρ) * (ρ⁻¹ ^ 2 *
                  ∫ y in vec3Ball z.1 ρ, |p (y, t)| ^ (3 / 2 : ℝ)))) ∧
          pressureD p z r ≤ lin34AbsoluteConstant *
            ((ρ / r) ^ 2 * pressureChat u z ρ +
              (r / ρ) * pressureD p z ρ))) ∧
        pressureD p z r ≤ CKN.Core.Endgame.theoremALin34Constant q *
          ((ρ / r) ^ 2 * pressureChat u z ρ +
            (r / ρ) * pressureD p z ρ +
            (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ))) := by
  intro Ω I u Du p f hsol z r ρ hρ hr hhalf hsub
  have hforce := CKN.Core.Endgame.theoremA_hLin34_of_sws q hsol hρ hr hhalf hsub
  refine ⟨?_, hforce⟩
  intro hdiv
  have hpoint := lin34_slice_pointwise_bound_ae_of_sws_spaceTimeDivergenceFree
    hsol hρ hr hhalf hsub hdiv
  have hpointCommon : ∀ᵐ t ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      r⁻¹ ^ 2 * lin34PressureSlice p z r t ≤
        lin34AbsoluteConstant *
          ((ρ / r) ^ 2 * lin34G u z ρ t + (r / ρ) * lin34H p z ρ t) := by
    filter_upwards [hpoint] with t ht
    exact ht.trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (lin34F_local_nonneg hρ hr t))
  have hρr : r ≤ ρ := by linarith only [hhalf, hρ]
  let F : ℝ → ℝ := lin34F p z r
  let G : ℝ → ℝ := lin34G u z ρ
  let H : ℝ → ℝ := lin34H p z ρ
  let μ : Measure ℝ := volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)
  have hpointF : ∀ᵐ t ∂μ,
      F t ≤ lin34AbsoluteConstant *
        ((ρ / r) ^ 2 * G t + (r / ρ) * H t) := by
    filter_upwards [hpointCommon] with t ht
    by_cases hmem : t ∈ Ioc (z.2 - r ^ 2) z.2
    · dsimp only [F, lin34F]
      rw [Set.indicator_of_mem hmem]
      simpa [G, H, lin34G, lin34H, lin34VelocitySlice, lin34PressureSlice] using ht
    · dsimp only [F, lin34F]
      rw [Set.indicator_of_notMem hmem]
      exact mul_nonneg lin34AbsoluteConstant_nonneg
        (lin34F_local_nonneg hρ hr t)
  have hF : Integrable F μ := by
    dsimp [F, μ]
    exact lin34F_integrable hsol hρ hr hρr hsub
  have hG : Integrable G μ := by
    dsimp [G, μ]
    exact lin34G_integrable hsol hρ hsub
  have hH : Integrable H μ := by
    dsimp [H, μ]
    exact lin34H_integrable hsol hρ hsub
  have hDr : pressureD p z r = ∫ t, F t ∂μ := by
    dsimp [F, μ]
    exact lin34_pressureD_inner_eq_integral hsol hρ hr hρr hsub
  have hDρ : pressureD p z ρ = ∫ t, H t ∂μ := by
    dsimp [H, μ]
    exact lin34_pressureD_eq_integral hsol hρ hsub
  have hChat : pressureChat u z ρ = ∫ t, G t ∂μ := by
    dsimp [G, μ]
    exact lin34_pressureChat_eq_integral hsol hρ hsub
  have hintegrated := pressureD_integrated_from_slices hF hG hH hpointF hDr hDρ hChat
  refine ⟨?_, hintegrated⟩
  · filter_upwards [hpointCommon] with t ht
    simpa [lin34PressureSlice, lin34G, lin34H, lin34VelocitySlice] using ht

end CKN

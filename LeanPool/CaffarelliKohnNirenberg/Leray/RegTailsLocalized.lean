/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsEstimates
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim

/-!
# Localized energy identities for regularized Leray solutions

Compact spatial tests in `lem:reg-local-energy` yield an interval energy
identity for every compact spatial cutoff.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regTails_integral_on_positiveSpace_eq_iterated
    (F : Vec3 × ℝ → ℝ)
    (hF : Integrable F
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))))) :
    (∫ z in (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ), F z
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ t in Ioi (0 : ℝ), ∫ x : Vec3, F (x, t) ∂volume ∂volume := by
  have hMeasure :
      (volume : Measure (Vec3 × ℝ)).restrict
          ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) =
        (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) = _
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
    simp [Measure.restrict_univ]
  calc
    _ = ∫ z : Vec3 × ℝ, F z ∂((volume : Measure (Vec3 × ℝ)).restrict
          ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ))) := rfl
    _ = ∫ z : Vec3 × ℝ, F z ∂
          ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) := by
      rw [hMeasure]
    _ = ∫ t in Ioi (0 : ℝ), ∫ x : Vec3, F (x, t) ∂volume ∂volume :=
      integral_prod_symm F hF

private theorem regTails_spatialPartial_square
    (u : ParabolicPoint → Vec3) (i j : Fin 3)
    (hU : ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => u (z.1, z.2) i)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (z : Vec3 × ℝ) (hz : z ∈ (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) :
    spatialPartial (fun y : ParabolicPoint => u y i ^ (2 : ℕ)) j z =
      2 * u (z.1, z.2) i *
        spatialPartial (fun y : ParabolicPoint => u y i) j z := by
  have hUdiff := regUniform_contDiffOn_spatialSlice_differentiableAt
    (isOpen_univ.prod isOpen_Ioi) hU hz
  have hUdiff' : DifferentiableAt ℝ
      (fun x : Vec3 => u (x, z.2) i) z.1 := by
    simpa using hUdiff
  change (fderiv ℝ (fun x : Vec3 => u (x, z.2) i ^ (2 : ℕ)) z.1)
      (basisVec j) = 2 * u (z.1, z.2) i *
        (fderiv ℝ (fun x : Vec3 => u (x, z.2) i) z.1) (basisVec j)
  have hpow : (fun x : Vec3 => u (x, z.2) i ^ (2 : ℕ)) =
      (fun x : Vec3 => u (x, z.2) i) ^ (2 : ℕ) := rfl
  rw [hpow, fderiv_pow 2 hUdiff']
  simp

/-- Spatial integration by parts transfers the compact cutoff Laplacian onto
the regularized velocity in the positive time region. This is the localized
form of the calculation in `lem:reg-tails`. -/
theorem regTails_laplacian_ibp
    (u : ParabolicPoint → Vec3) (q : Vec3 → ℝ)
    (η : ℝ → ℝ) (i j : Fin 3)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqc : HasCompactSupport q)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηI : tsupport η ⊆ Ioi (0 : ℝ))
    (hUcont : ∀ k : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => u (z.1, z.2) k)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hDcont : ∀ k j : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial
        (fun y : ParabolicPoint => u y k) j z)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hUdiff : ∀ k : Fin 3, ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => u (z.1, z.2) k)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ))) :
    (∫ z in (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ),
      u (z.1, z.2) i ^ (2 : ℕ) *
        spatialSecondPartial (fun y : ParabolicPoint => q y.1) j j z * η z.2
        ∂(volume : Measure (Vec3 × ℝ))) =
      -2 * ∫ z in (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ),
        u (z.1, z.2) i *
          spatialPartial (fun y : ParabolicPoint => u y i) j z *
          spatialPartial (fun y : ParabolicPoint => q y.1) j z * η z.2
          ∂(volume : Measure (Vec3 × ℝ)) := by
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  let qST : Vec3 × ℝ → ℝ := fun z => q z.1
  let F : Vec3 × ℝ → ℝ := fun z => u (z.1, z.2) i ^ (2 : ℕ)
  let qi : Vec3 → ℝ := fun x => (fderiv ℝ q x) (basisVec j)
  let Q : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (show ParabolicPoint → ℝ from qST) j z
  let G : Vec3 × ℝ → ℝ := fun z =>
    Q z * η z.2
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioi
  have hqST : ContDiff ℝ (⊤ : ℕ∞) qST := by
    exact hq.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff
  have hqi : HasCompactSupport qi := hqc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hqpartial : ContDiff ℝ (⊤ : ℕ∞)
      Q := by
    exact spatialPartial_contDiff hqST j
  have hGfull : ContDiff ℝ (⊤ : ℕ∞) G := by
    exact hqpartial.mul (hη.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff)
  have hGcont : ContinuousOn G S := hGfull.continuous.continuousOn
  have hGpartialCont : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from G) j z) S := by
    exact (spatialPartial_contDiff hGfull j).continuous.continuousOn
  have hGsupportBase : Function.support G ⊆ tsupport qi ×ˢ tsupport η := by
    intro z hz
    have hGz : G z ≠ 0 := Function.mem_support.mp hz
    have hqiEq (z : Vec3 × ℝ) : Q z = qi z.1 := by
      simp [Q, qST, qi, spatialPartial]
    constructor
    · by_contra hx
      have hqz : qi z.1 = 0 := by
        by_contra hne
        exact hx (subset_tsupport qi (Function.mem_support.mpr hne))
      exact hGz (by simp [G, hqiEq z, hqz])
    · by_contra ht
      have hηz : η z.2 = 0 := by
        by_contra hne
        exact ht (subset_tsupport η (Function.mem_support.mpr hne))
      exact hGz (by simp [G, hηz])
  have hGsupportClosed : IsClosed (tsupport qi ×ˢ tsupport η) :=
    (hqi.isCompact.prod hηc.isCompact).isClosed
  have hGtsupport : tsupport G ⊆ tsupport qi ×ˢ tsupport η :=
    closure_minimal hGsupportBase hGsupportClosed
  have hGcompact : HasCompactSupport G :=
    (hqi.isCompact.prod hηc.isCompact).of_isClosed_subset
      (isClosed_tsupport (f := G)) hGtsupport
  have hGsupportS : tsupport G ⊆ S := by
    exact hGtsupport.trans (Set.prod_mono (Set.subset_univ _) hηI)
  have hFcont : ContinuousOn F S := by
    change ContinuousOn (fun z : Vec3 × ℝ => u (z.1, z.2) i ^ (2 : ℕ)) S
    exact (hUcont i).pow 2
  have hFpartialCont : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from F) j z) S := by
    have hbase : ContinuousOn
        (fun z : Vec3 × ℝ => 2 * u (z.1, z.2) i *
      spatialPartial (fun y : ParabolicPoint => u y i) j z) S := by
      have hprod :=
        ((show ContinuousOn (fun _ : Vec3 × ℝ => (2 : ℝ)) S from continuousOn_const).mul
          (hUcont i)).mul (hDcont i j)
      change ContinuousOn
        (((fun _ : Vec3 × ℝ => (2 : ℝ)) *
          (fun z : Vec3 × ℝ => u (z.1, z.2) i)) *
            (fun z : Vec3 × ℝ =>
              spatialPartial (fun y : ParabolicPoint => u y i) j z)) S
      exact hprod
    apply hbase.congr
    intro z hz
    change spatialPartial (fun y : ParabolicPoint => u y i ^ (2 : ℕ)) j z = _
    exact regTails_spatialPartial_square u i j (hUdiff i) z hz
  have hFdiff : ∀ z ∈ S,
      DifferentiableAt ℝ (fun x : Vec3 => F (x, z.2)) z.1 := by
    intro z hz
    have hu := regUniform_contDiffOn_spatialSlice_differentiableAt
      hSopen (hUdiff i) hz
    have hu' : DifferentiableAt ℝ (fun x : Vec3 => u (x, z.2) i) z.1 := by
      simpa using hu
    have hp : DifferentiableAt ℝ
        (fun x : Vec3 => u (x, z.2) i ^ (2 : ℕ)) z.1 := hu'.pow 2
    simpa [F] using hp
  have hGdiff : ∀ z ∈ S,
      DifferentiableAt ℝ (fun x : Vec3 => G (x, z.2)) z.1 := by
    intro z hz
    have hGz : DifferentiableAt ℝ G z := hGfull.differentiable (by norm_num) z
    have hmap : DifferentiableAt ℝ (fun x : Vec3 => (x, z.2)) z.1 := by fun_prop
    convert hGz.comp z.1 hmap using 1
    rfl
  have hIBP := regUniform_integral_mul_spatialPartial_eq_neg
    (i := j) hSopen hFcont hFpartialCont hFdiff hGcont hGpartialCont
    hGdiff hGcompact hGsupportS
  have hGpartial (z : Vec3 × ℝ) :
      spatialPartial (show ParabolicPoint → ℝ from G) j z =
        spatialSecondPartial (show ParabolicPoint → ℝ from qST) j j z * η z.2 := by
    have hpart : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec3 × ℝ => spatialPartial
          (show ParabolicPoint → ℝ from qST) j y) := by
      exact spatialPartial_contDiff hqST j
    have hformula := spatialPartial_mul_time (χ := η) hpart j z
    change spatialPartial (fun y : Vec3 × ℝ => Q y * η y.2) j z = _
    calc
      _ = spatialPartial (fun y : Vec3 × ℝ => Q y * η y.2) j z := rfl
      _ = spatialPartial Q j z * η z.2 := hformula
      _ = _ := rfl
  have hFpartial (z : Vec3 × ℝ) (hz : z ∈ S) :
      spatialPartial (show ParabolicPoint → ℝ from F) j z =
        2 * u (z.1, z.2) i *
          spatialPartial (fun y : ParabolicPoint => u y i) j z := by
    change spatialPartial (fun y : ParabolicPoint => u y i ^ (2 : ℕ)) j z = _
    exact regTails_spatialPartial_square u i j (hUdiff i) z hz
  calc
    _ = ∫ z in S, F z *
        spatialPartial (show ParabolicPoint → ℝ from G) j z
        ∂(volume : Measure (Vec3 × ℝ)) := by
          apply setIntegral_congr_fun
            (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi)
          intro z hz
          change u ((z.1, z.2) : ParabolicPoint) i ^ (2 : ℕ) *
            spatialSecondPartial (show ParabolicPoint → ℝ from qST) j j z * η z.2 =
            F z * spatialPartial (show ParabolicPoint → ℝ from G) j z
          rw [hGpartial z]
          dsimp [F]
          ring
    _ = -∫ z in S,
        spatialPartial (show ParabolicPoint → ℝ from F) j z * G z
        ∂(volume : Measure (Vec3 × ℝ)) := hIBP
    _ = -2 * ∫ z in S,
        u (z.1, z.2) i *
          spatialPartial (fun y : ParabolicPoint => u y i) j z *
          spatialPartial (fun y : ParabolicPoint => q y.1) j z * η z.2
        ∂(volume : Measure (Vec3 × ℝ)) := by
            have hInt : (∫ z : Vec3 × ℝ in S,
              spatialPartial (show ParabolicPoint → ℝ from F) j z * G z
              ∂(volume : Measure (Vec3 × ℝ))) =
              ∫ z : Vec3 × ℝ in S,
                2 * (u (z.1, z.2) i *
                  spatialPartial (fun y : ParabolicPoint => u y i) j z *
                  spatialPartial (fun y : ParabolicPoint => q y.1) j z * η z.2)
                ∂(volume : Measure (Vec3 × ℝ)) := by
              apply setIntegral_congr_fun
                (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi)
              intro z hz
              change spatialPartial (show ParabolicPoint → ℝ from F) j z * G z = _
              rw [hFpartial z hz]
              simp [G, Q, qST, spatialPartial]
              ring_nf
            change -(∫ z : Vec3 × ℝ in S,
              spatialPartial (show ParabolicPoint → ℝ from F) j z * G z
              ∂(volume : Measure (Vec3 × ℝ))) = _
            rw [hInt, integral_const_mul]
            ring

private theorem regTails_intervalIntegral_eq_sub_of_smooth_test_identity
    {I : Set ℝ} (hI : IsOpen I) (F f g : ℝ → ℝ)
    (hFcont : ContinuousOn F I)
    (hfloc : LocallyIntegrableOn f I volume)
    (hgloc : LocallyIntegrableOn g I)
    (hFderiv : ∀ t ∈ I, HasDerivAt F (f t) t)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η →
      HasCompactSupport η → tsupport η ⊆ I →
      ∫ x : ℝ, F x * (fderiv ℝ η x) 1 ∂volume =
        -∫ x : ℝ, g x * η x ∂volume)
    {s t : ℝ} (hst : s ≤ t) (hIcc : Icc s t ⊆ I) :
    F t - F s = ∫ x in s..t, g x ∂volume := by
  have hResidual : LocallyIntegrableOn (fun x => f x - g x) I volume :=
    hfloc.sub hgloc
  have hDerivAeVolume : ∀ᵐ x : ℝ ∂volume, x ∈ I → f x - g x = 0 := by
    apply hI.ae_eq_zero_of_integral_contDiff_smul_eq_zero hResidual
    intro η hη hηc hηI
    let K : Set ℝ := tsupport η
    have hKcompact : IsCompact K := hηc
    have hη_cont : Continuous η := hη.continuous
    have hη'_cont : Continuous (fun x : ℝ => (fderiv ℝ η x) 1) := by
      have hfd := hη.continuous_fderiv (by norm_num)
      exact hfd.clm_apply continuous_const
    have hη'_compact : HasCompactSupport (fun x : ℝ => (fderiv ℝ η x) 1) :=
      hηc.fderiv_apply (𝕜 := ℝ) (1 : ℝ)
    have hflocK : IntegrableOn f K volume :=
      hfloc.integrableOn_compact_subset hηI hKcompact
    have hglocK : IntegrableOn g K volume :=
      hgloc.integrableOn_compact_subset hηI hKcompact
    have hIntfηK : IntegrableOn (fun x => f x * η x) K volume :=
      hflocK.mul_continuousOn hη_cont.continuousOn hKcompact
    have hIntgηK : IntegrableOn (fun x => g x * η x) K volume :=
      hglocK.mul_continuousOn hη_cont.continuousOn hKcompact
    have hfsupport : Function.support (fun x : ℝ => f x * η x) ⊆ K := by
      intro x hx
      apply subset_tsupport η
      apply Function.mem_support.mpr
      intro hηx
      have hprod : f x * η x ≠ 0 := Function.mem_support.mp hx
      exact hprod (by rw [hηx, mul_zero])
    have hgsupport : Function.support (fun x : ℝ => g x * η x) ⊆ K := by
      intro x hx
      apply subset_tsupport η
      apply Function.mem_support.mpr
      intro hηx
      have hprod : g x * η x ≠ 0 := Function.mem_support.mp hx
      exact hprod (by rw [hηx, mul_zero])
    have hIntfη : Integrable (fun x => f x * η x) volume := by
      exact (integrableOn_iff_integrable_of_support_subset hfsupport).mp hIntfηK
    have hIntgη : Integrable (fun x => g x * η x) volume := by
      exact (integrableOn_iff_integrable_of_support_subset hgsupport).mp hIntgηK
    have hFηK : IntegrableOn (fun x => F x * η x) K volume := by
      exact (hFcont.mono hηI).mul hη_cont.continuousOn |>.integrableOn_compact
        hKcompact
    have hFηsupport : Function.support (fun x : ℝ => F x * η x) ⊆ K := by
      intro x hx
      apply subset_tsupport η
      apply Function.mem_support.mpr
      intro hηx
      have hprod : F x * η x ≠ 0 := Function.mem_support.mp hx
      exact hprod (by rw [hηx, mul_zero])
    have hIntFη : Integrable (fun x => F x * η x) volume :=
      (integrableOn_iff_integrable_of_support_subset hFηsupport).mp hFηK
    have hη'derivSupport : tsupport (fun x : ℝ => (fderiv ℝ η x) 1) ⊆ K :=
      tsupport_fderiv_apply_subset ℝ (1 : ℝ)
    have hFη'K : IntegrableOn
        (fun x => F x * (fderiv ℝ η x) 1) K volume := by
      exact (hFcont.mono hηI).mul hη'_cont.continuousOn |>.integrableOn_compact
        hKcompact
    have hFη'support : Function.support
        (fun x : ℝ => F x * (fderiv ℝ η x) 1) ⊆ K := by
      intro x hx
      apply hη'derivSupport
      apply subset_tsupport _
      apply Function.mem_support.mpr
      intro hη'x
      have hprod : F x * (fderiv ℝ η x) 1 ≠ 0 := Function.mem_support.mp hx
      exact hprod (by rw [hη'x, mul_zero])
    have hIntFη' : Integrable
        (fun x => F x * (fderiv ℝ η x) 1) volume :=
      (integrableOn_iff_integrable_of_support_subset hFη'support).mp hFη'K
    have hFline : ∀ x ∈ tsupport η,
        HasLineDerivAt ℝ F (f x) x (1 : ℝ) := by
      intro x hx
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
        (hFderiv x (hηI hx)).hasFDerivAt.hasLineDerivAt (1 : ℝ)
    have hηline : ∀ x ∈ tsupport F,
        HasLineDerivAt ℝ η ((fderiv ℝ η x) 1) x (1 : ℝ) := by
      intro x hx
      exact (hη.differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt 1
    have hParts := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℝ)
      (f := F) (f' := f) (g := η)
      (g' := fun x => (fderiv ℝ η x) 1) (v := (1 : ℝ))
      hIntfη hIntFη' hIntFη hFline hηline
    have hWeakη := hweak η hη hηc hηI
    have hIntegralEq : (∫ x : ℝ, f x * η x ∂volume) =
        ∫ x : ℝ, g x * η x ∂volume := by
      apply neg_injective
      exact hParts.symm.trans hWeakη
    have hProductEq : (fun x : ℝ => η x * (f x - g x)) =
        fun x => f x * η x - g x * η x := by
      funext x
      ring
    have hIntegralProduct : (∫ x : ℝ, η x * (f x - g x) ∂volume) =
        ∫ x : ℝ, f x * η x - g x * η x ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrFun hProductEq x
    have hIntegralZero : (∫ x : ℝ, η x * (f x - g x) ∂volume) = 0 := by
      rw [hIntegralProduct, integral_sub hIntfη hIntgη, hIntegralEq, sub_self]
    exact hIntegralZero
  have hDerivAe : ∀ᵐ x ∂(volume.restrict I), f x - g x = 0 := by
    filter_upwards [ae_restrict_of_ae hDerivAeVolume,
      ae_restrict_mem hI.measurableSet] with x hx hxI
    exact hx hxI
  have hResidualEq : f =ᵐ[volume.restrict I] g := by
    filter_upwards [hDerivAe] with x hx
    exact sub_eq_zero.mp hx
  have hfIcc : IntegrableOn f (Icc s t) volume :=
    hfloc.integrableOn_compact_subset hIcc isCompact_Icc
  have hfInterval : IntervalIntegrable f volume s t := by
    refine ⟨hfIcc.mono_set Ioc_subset_Icc_self, ?_⟩
    simp [Ioc_eq_empty (not_lt.mpr hst)]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hst (hFcont.mono hIcc)
    (fun x hx => hFderiv x (hIcc (Ioo_subset_Icc_self hx))) hfInterval
  have hIocSubset : Ioc s t ⊆ I := (Ioc_subset_Icc_self).trans hIcc
  have hResidualIoc := ae_restrict_of_ae_restrict_of_subset hIocSubset hResidualEq
  have hIocAE : ∀ᵐ x : ℝ ∂volume, x ∈ Ioc s t → f x = g x := by
    exact (ae_restrict_iff' measurableSet_Ioc).mp hResidualIoc
  have hIntegralEq : ∫ x in s..t, f x ∂volume =
      ∫ x in s..t, g x ∂volume := by
    apply intervalIntegral.integral_congr_ae
    simpa [uIoc_of_le hst] using hIocAE
  rw [← hFTC, hIntegralEq]

/-- A continuous scalar weak time identity gives the corresponding interval
identity on every positive time interval. -/
theorem regTails_intervalIntegral_eq_sub_of_weak_identity
    (F g : ℝ → ℝ)
    (hFcont : ContinuousOn F (Ioi (0 : ℝ)))
    (hGcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η →
      HasCompactSupport η → tsupport η ⊆ Ioi (0 : ℝ) →
      ∫ x : ℝ, F x * deriv η x ∂volume =
        -∫ x : ℝ, g x * η x ∂volume)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    F t - F s = ∫ x in s..t, g x ∂volume := by
  let a : ℝ := s / 2
  let b : ℝ := t + 1
  let c : ℝ := (s + t) / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have has : a < s := by dsimp [a]; linarith only [hs]
  have htb : t < b := by
    dsimp [b]
    linarith only [show (0 : ℝ) < 1 by norm_num]
  have hab : a < b := lt_trans has (lt_trans hst htb)
  have hta : s ∈ Ioo a b := ⟨has, lt_trans hst htb⟩
  have htt : t ∈ Ioo a b := ⟨lt_trans has hst, htb⟩
  have hcBounds : s < c ∧ c < t := by
    dsimp [c]
    constructor <;> linarith only [hst]
  have htc : c ∈ Ioo a b :=
    ⟨lt_trans has hcBounds.1, lt_trans hcBounds.2 htb⟩
  have hUsub : Ioo a b ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_trans ha hx.1
  have hweakOn : CKN.HasWeakDerivOn (Ioo a b) F g := by
    intro η hη
    rcases hη with ⟨hηsmooth, hηcompact, hηsupport⟩
    have hηpositive : tsupport η ⊆ Ioi (0 : ℝ) := hηsupport.trans hUsub
    have hglobal := hweak η hηsmooth hηcompact hηpositive
    have hderivSupport : tsupport (deriv η) ⊆ Ioo a b :=
      (tsupport_deriv_subset (f := η)).trans hηsupport
    have hleft : (∫ x in Ioo a b, F x * deriv η x ∂volume) =
        ∫ x : ℝ, F x * deriv η x ∂volume := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hzero : deriv η x = 0 := by
        by_contra hne
        exact hx (hderivSupport
          (subset_tsupport (f := deriv η) (Function.mem_support.mpr hne)))
      simp [hzero]
    have hright : (∫ x in Ioo a b, g x * η x ∂volume) =
        ∫ x : ℝ, g x * η x ∂volume := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hzero : η x = 0 := by
        by_contra hne
        exact hx (hηsupport
          (subset_tsupport (f := η) (Function.mem_support.mpr hne)))
      simp [hzero]
    rw [hleft, hright]
    exact hglobal
  have hFloc : LocallyIntegrableOn F (Ioo a b) volume :=
    (hFcont.mono hUsub).locallyIntegrableOn isOpen_Ioo.measurableSet
  have hGloc : LocallyIntegrableOn g (Ioo a b) volume :=
    (hGcont.mono hUsub).locallyIntegrableOn isOpen_Ioo.measurableSet
  obtain ⟨C, hrep⟩ := CKN.eq_const_add_intervalIntegral_of_continuous_weakDeriv
    hab htc hFloc hGloc hweakOn
    (hFcont.mono hUsub)
  have hFs : F s = C + ∫ r in c..s, g r ∂volume := hrep s hta
  have hFt : F t = C + ∫ r in c..t, g r ∂volume := hrep t htt
  have hIccSC : Icc s c ⊆ Ioo a b := by
    intro x hx
    exact ⟨lt_of_lt_of_le has hx.1,
      lt_trans (lt_of_le_of_lt hx.2 hcBounds.2) htb⟩
  have hIccCT : Icc c t ⊆ Ioo a b := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_trans has hcBounds.1) hx.1,
      lt_of_le_of_lt hx.2 htb⟩
  have hGsc : IntegrableOn g (Icc s c) volume :=
    hGloc.integrableOn_compact_subset hIccSC isCompact_Icc
  have hGct : IntegrableOn g (Icc c t) volume :=
    hGloc.integrableOn_compact_subset hIccCT isCompact_Icc
  have hGcT : IntervalIntegrable g volume c t := by
    refine ⟨hGct.mono_set Ioc_subset_Icc_self, ?_⟩
    simp [Ioc_eq_empty (not_lt.mpr hcBounds.2.le)]
  have hGcS : IntervalIntegrable g volume c s := by
    have hSc : IntervalIntegrable g volume s c := by
      refine ⟨hGsc.mono_set Ioc_subset_Icc_self, ?_⟩
      simp [Ioc_eq_empty (not_lt.mpr hcBounds.1.le)]
    exact hSc.symm
  calc
    F t - F s =
        (∫ r in c..t, g r ∂volume) - ∫ r in c..s, g r ∂volume := by
          rw [hFt, hFs]
          ring
    _ = ∫ r in s..t, g r ∂volume :=
      intervalIntegral.integral_interval_sub_left hGcT hGcS

/-- Fubini separates a compact positive time factor from a locally continuous
space-time coefficient. -/
theorem regTails_timeFactor_integral
    (A : Vec3 × ℝ → ℝ) (η : ℝ → ℝ)
    (hInt : Integrable (fun z : Vec3 × ℝ => A z * η z.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))))) :
    (∫ z in (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ),
      A z * η z.2 ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ t in Ioi (0 : ℝ), (∫ x : Vec3, A (x, t) ∂volume) * η t ∂volume := by
  have hIter := regTails_integral_on_positiveSpace_eq_iterated
    (fun z : Vec3 × ℝ => A z * η z.2) hInt
  calc
    (∫ z in (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ),
        A z * η z.2 ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ t in Ioi (0 : ℝ), ∫ x : Vec3, A (x, t) * η t ∂volume ∂volume := hIter
    _ = ∫ t in Ioi (0 : ℝ),
        (∫ x : Vec3, A (x, t) ∂volume) * η t ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          change (∫ x : Vec3, A (x, t) * η t ∂volume) =
            (∫ x : Vec3, A (x, t) ∂volume) * η t
          rw [integral_mul_const]

private theorem regTails_integral_continuousOn_of_compact_support
    (F : Vec3 × ℝ → ℝ) (K : Set Vec3)
    (hF : ContinuousOn F ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hK : IsCompact K)
    (hzero : ∀ t x, 0 < t → x ∉ K → F (x, t) = 0) :
    ContinuousOn (fun t : ℝ => ∫ x : Vec3, F (x, t) ∂volume)
      (Ioi (0 : ℝ)) := by
  have hmapCont : ContinuousOn (fun z : ℝ × Vec3 => (z.2, z.1))
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set Vec3)) := by
    fun_prop
  have hmap : MapsTo (fun z : ℝ × Vec3 => (z.2, z.1))
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set Vec3))
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) := by
    intro z hz
    exact ⟨Set.mem_univ _, hz.1⟩
  have hjoint : ContinuousOn
      (Function.uncurry (fun t x => F (x, t)))
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set Vec3)) := by
    exact hF.comp hmapCont hmap
  apply (continuousOn_integral_of_compact_support hK hjoint ?_)
  intro t x ht hx
  exact hzero t x ht hx

/-- The localized kinetic energy associated with a compact spatial weight. -/
@[expose]
def regTailsEnergyWeight
    (u : ParabolicPoint → Vec3) (q : Vec3 → ℝ) (t : ℝ) : ℝ :=
  ∫ x : Vec3, (vec3EuclideanNorm (u (x, t))) ^ (2 : ℕ) * q x ∂volume

/-- The flux form of the localized kinetic energy derivative in
`lem:reg-tails`. -/
@[expose]
def regTailsLocalizedSource
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (J : ParabolicPoint → Vec3)
    (q : Vec3 → ℝ) (z : ParabolicPoint) : ℝ :=
  -2 * spatialGradientSq u D z * q z.1 -
    (2 * ∑ i : Fin 3, ∑ j : Fin 3,
      u z i * D z i j *
        spatialPartial (fun y : ParabolicPoint => q y.1) j z) +
    ∑ j : Fin 3,
      ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z j +
        2 * p z * u z j) *
          spatialPartial (fun y : ParabolicPoint => q y.1) j z

/-- Compact spatial weights make the localized energy and its flux source
continuous functions of positive time. -/
theorem regTails_localized_profiles_continuous
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (J : ParabolicPoint → Vec3)
    (q : Vec3 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqc : HasCompactSupport q)
    (hUcont : ∀ i : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => u (z.1, z.2) i)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hDcont : ∀ i j : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => D (z.1, z.2) i j)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hPcont : ContinuousOn (fun z : Vec3 × ℝ => p (z.1, z.2))
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hJcont : ∀ i : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => J (z.1, z.2) i)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ))) :
    ContinuousOn (regTailsEnergyWeight u q) (Ioi (0 : ℝ)) ∧
      ContinuousOn (fun t : ℝ => ∫ x : Vec3,
        regTailsLocalizedSource u D p J q (x, t) ∂volume)
        (Ioi (0 : ℝ)) := by
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  let qST : Vec3 × ℝ → ℝ := fun z => q z.1
  let e : Vec3 × ℝ → ℝ := fun z =>
    (vec3EuclideanNorm (u (z.1, z.2))) ^ (2 : ℕ)
  let d : Vec3 × ℝ → ℝ := fun z =>
    spatialGradientSq u D (z.1, z.2)
  let src : Vec3 × ℝ → ℝ := fun z =>
    regTailsLocalizedSource u D p J q (z.1, z.2)
  have hqST : ContDiff ℝ (⊤ : ℕ∞) qST := by
    exact hq.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff
  have hqjCont (j : Fin 3) : Continuous qST := by
    exact hqST.continuous
  have hqpartialCont (j : Fin 3) : Continuous
      (fun z : Vec3 × ℝ => spatialPartial
        (show ParabolicPoint → ℝ from qST) j z) :=
    (spatialPartial_contDiff hqST j).continuous
  have hqbaseOn : ContinuousOn (fun z : Vec3 × ℝ => q z.1) S := by
    simpa [qST] using hqST.continuous.continuousOn
  have hqpartOn (j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial
        (fun y : ParabolicPoint => q y.1) j z) S := by
    convert hqpartialCont j |>.continuousOn using 1
    rfl
  have hEcont : ContinuousOn e S := by
    unfold e
    have hvec : ContinuousOn (fun z : Vec3 × ℝ => u (z.1, z.2)) S := by
      apply continuousOn_pi.mpr
      exact hUcont
    exact (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_continuousOn
      hvec).pow 2
  have hUcoord (i : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => u (z.1, z.2) i) S := hUcont i
  have hDcoord (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => D (z.1, z.2) i j) S := hDcont i j
  have hJcoord (i : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => J (z.1, z.2) i) S := hJcont i
  have hdcont : ContinuousOn d S := by
    unfold d spatialGradientSq
    fun_prop
  have hsrccont : ContinuousOn src S := by
    unfold src regTailsLocalizedSource
    have hfirst : ContinuousOn (fun z : Vec3 × ℝ =>
        -2 * d z * q z.1) S :=
      (continuousOn_const.mul hdcont).mul hqbaseOn
    have hsecondSum : ContinuousOn (fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, ∑ j : Fin 3,
          u (z.1, z.2) i * D (z.1, z.2) i j *
            spatialPartial (fun y : ParabolicPoint => q y.1) j z) S := by
      apply continuousOn_finsetSum
      intro i hi
      apply continuousOn_finsetSum
      intro j hj
      exact ((hUcoord i).mul (hDcoord i j)).mul (hqpartOn j)
    have hsecond : ContinuousOn (fun z : Vec3 × ℝ =>
        -(2 * ∑ i : Fin 3, ∑ j : Fin 3,
          u (z.1, z.2) i * D (z.1, z.2) i j *
            spatialPartial (fun y : ParabolicPoint => q y.1) j z)) S := by
      exact (continuousOn_const.mul hsecondSum).neg
    have hPcoord : ContinuousOn (fun z : Vec3 × ℝ => p (z.1, z.2)) S := hPcont
    have hthirdSum : ContinuousOn (fun z : Vec3 × ℝ =>
        ∑ j : Fin 3,
          (e z * J (z.1, z.2) j +
            2 * p (z.1, z.2) * u (z.1, z.2) j) *
              spatialPartial (fun y : ParabolicPoint => q y.1) j z) S := by
      apply continuousOn_finsetSum
      intro j hj
      exact ((hEcont.mul (hJcoord j)).add
        ((continuousOn_const.mul hPcoord).mul (hUcoord j))).mul (hqpartOn j)
    change ContinuousOn (fun z : Vec3 × ℝ =>
      -2 * d z * q z.1 -
        (2 * ∑ i : Fin 3, ∑ j : Fin 3,
          u (z.1, z.2) i * D (z.1, z.2) i j *
            spatialPartial (fun y : ParabolicPoint => q y.1) j z) +
        ∑ j : Fin 3,
          (e z * J (z.1, z.2) j +
            2 * p (z.1, z.2) * u (z.1, z.2) j) *
              spatialPartial (fun y : ParabolicPoint => q y.1) j z) S
    apply ((hfirst.add hsecond).add hthirdSum).congr
    intro z hz
    simp only [Pi.add_apply, sub_eq_add_neg]
  have hqZero (x : Vec3) (hx : x ∉ tsupport q) : q x = 0 := by
    by_contra hne
    exact hx (subset_tsupport q (Function.mem_support.mpr hne))
  have hqjZero (j : Fin 3) (x : Vec3)
      (hx : x ∉ tsupport q) (t : ℝ) :
      spatialPartial (fun y : ParabolicPoint => q y.1) j (x, t) = 0 := by
    have hqjSupport : tsupport (fun y : Vec3 =>
        (fderiv ℝ q y) (basisVec j)) ⊆ tsupport q :=
      tsupport_fderiv_apply_subset ℝ (basisVec j)
    have hqjEq : spatialPartial (fun y : ParabolicPoint => q y.1) j
        (x, t) = (fderiv ℝ q x) (basisVec j) := by
      rfl
    rw [hqjEq]
    by_contra hne
    exact hx (hqjSupport (subset_tsupport _ (Function.mem_support.mpr hne)))
  have hK : IsCompact (tsupport q) := hqc.isCompact
  have hFzero : ∀ t x, 0 < t → x ∉ tsupport q → e (x, t) * q x = 0 := by
    intro t x ht hx
    simp [hqZero x hx]
  have hFcont := regTails_integral_continuousOn_of_compact_support
    (fun z => e z * q z.1) (tsupport q) (by
      have he : ContinuousOn e S := hEcont
      have hq' : ContinuousOn (fun z : Vec3 × ℝ => q z.1) S :=
        hqST.continuous.continuousOn
      exact he.mul hq') hK hFzero
  have hSrczero : ∀ t x, 0 < t → x ∉ tsupport q → src (x, t) = 0 := by
    intro t x ht hx
    unfold src regTailsLocalizedSource
    have hqj (j : Fin 3) :
        spatialPartial (fun y : ParabolicPoint => q y.1) j (x, t) = 0 :=
      hqjZero j x hx t
    simp [hqZero x hx, hqj]
  have hGcont := regTails_integral_continuousOn_of_compact_support
    src (tsupport q) hsrccont hK hSrczero
  refine ⟨?_, hGcont⟩
  unfold regTailsEnergyWeight
  exact hFcont

end CKN.Leray

end

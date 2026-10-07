/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureOrthogonality
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTestLp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevBall
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilitySliceGradientCommon
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative.ProductH1
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.UniformCutoffFamilySeparated
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Time differentiation through the Leray projection

The L² Fourier construction of the Leray projection is a bounded linear map.
This file records the curve-calculus consequence used when differentiating
the projected evolution equation (`prop:lps-smoothing`).
-/

public section

open MeasureTheory
open Set
open scoped ENNReal
open CKN
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

open CKN.Leray

/-- Gives space-time points the product normed additive group structure for smoothing. -/
local instance smoothingTimeRegularityPointNormedAddCommGroup :
    NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- Gives space-time points the product real normed space structure for smoothing. -/
local instance smoothingTimeRegularityPointNormedSpace :
    NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- The strong weak equation is pressure-free when tested against a smooth
compactly supported solenoidal field (`prop:lps-smoothing`). -/
theorem lps_strong_solution_weak_equation_of_divFree_test
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsLpsStrongSolution t₀ t₁ u Du p)
    (φ : ParabolicPoint → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Ioo t₀ t₁))
    (hdiv : ∀ z : ParabolicPoint,
      ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁),
      (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial (fun y => φ y i) j z) = 0 := by
  have hweak := hsol.2.2.2.2.2 φ hφ
  calc
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z)
        = ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁),
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * spatialPartial (fun y => φ y i) j z
            - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by
            have hpressure : p z *
                (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) = 0 := by
              exact (congrArg (fun d : ℝ => p z * d) (hdiv z)).trans
                (mul_zero _)
            change
              (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
                - ∑ i : Fin 3, ∑ j : Fin 3,
                    u z i * u z j * spatialPartial (fun y => φ y i) j z
                + ∑ i : Fin 3, ∑ j : Fin 3,
                    Du z i j * spatialPartial (fun y => φ y i) j z) =
              (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
                - ∑ i : Fin 3, ∑ j : Fin 3,
                    u z i * u z j * spatialPartial (fun y => φ y i) j z
                + ∑ i : Fin 3, ∑ j : Fin 3,
                    Du z i j * spatialPartial (fun y => φ y i) j z
                - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
            rw [hpressure]
            ring
    _ = 0 := hweak

private theorem lps_spaceTimeTest_time_memLp_two
    {φ : Vec3 × ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (I : Set ℝ) :
    MemLp (timePartial (show ParabolicPoint → ℝ from φ)) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I)) := by
  exact (lps_spaceTimeTest_spatial_memLp_two
    (CKN.contDiff_timePartial hφ)
    (CKN.hasCompactSupport_timePartial hφc) I).1

private theorem lps_continuous_compact_support_bounded_spaceTime
    {φ : ParabolicPoint → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    ∃ C : ℝ, ∀ z : ParabolicPoint, ‖φ z‖ ≤ C := by
  by_cases hne : (tsupport φ).Nonempty
  · obtain ⟨z₀, hz₀, hmax⟩ := hφc.isCompact.exists_isMaxOn hne hφ.norm.continuousOn
    refine ⟨‖φ z₀‖, fun z => ?_⟩
    by_cases hz : z ∈ tsupport φ
    · exact hmax hz
    · have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [hzero]
  · have hzero : φ = 0 := by
      funext z
      by_contra hz
      exact hne ⟨z, (subset_tsupport (f := φ))
        (Function.mem_support.mpr hz)⟩
    exact ⟨0, by simp [hzero]⟩

private lemma lps_integral_weak_derivative_transfer
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {timeSource timeTarget convection diffSource diffTarget pressure : α → ℝ}
    (hTs : Integrable timeSource μ) (hTt : Integrable timeTarget μ)
    (hC : Integrable convection μ) (hDs : Integrable diffSource μ)
    (hDt : Integrable diffTarget μ) (hP : Integrable pressure μ)
    (hTime : (∫ z, timeSource z ∂μ) = -(∫ z, timeTarget z ∂μ))
    (hDiff : (∫ z, diffSource z ∂μ) = -(∫ z, diffTarget z ∂μ))
    (hWeak : (∫ z, -timeSource z - convection z + diffSource z - pressure z ∂μ) = 0) :
    (∫ z, timeTarget z - convection z - diffTarget z - pressure z ∂μ) = 0 := by
  have hWs := integral_sub ((hTs.neg.sub hC).add hDs) hP
  have hWa := integral_add (hTs.neg.sub hC) hDs
  have hWb := integral_sub hTs.neg hC
  have hT₁ := integral_sub ((hTt.sub hC).sub hDt) hP
  have hT₂ := integral_sub (hTt.sub hC) hDt
  have hT₃ := integral_sub hTt hC
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at hWs hWa hWb hT₁ hT₂ hT₃
  rw [hT₁, hT₂, hT₃]
  rw [hWs, hWa, hWb, integral_neg] at hWeak
  linarith only [hWeak, hTime, hDiff]

private lemma lps_weak_derivative_test_integrals
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hderivs : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ t₁)
      u Du D2u Dtu)
    (huL2 : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hDuL2 : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hD2uL2 : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hDtuL2 : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (φ : ParabolicPoint → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Ioo t₀ t₁)) :
    Integrable (fun z => ∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))) ∧
    Integrable (fun z => ∑ i : Fin 3, Dtu z i * φ z i)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))) ∧
    Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
        Du z i j * spatialPartial (fun y => φ y i) j z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))) ∧
    Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3, D2u z i j j * φ z i)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))) ∧
    (∫ z, (fun z => ∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z) z ∂(volume.restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁)))) =
      -(∫ z, (fun z => ∑ i : Fin 3, Dtu z i * φ z i) z ∂(volume.restrict (spaceTimeSet (Set.univ
        : Set Vec3) (Ioo t₀ t₁)))) ∧
    (∫ z, (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
        Du z i j * spatialPartial (fun y => φ y i) j z) z ∂(volume.restrict (spaceTimeSet
          (Set.univ : Set Vec3) (Ioo t₀ t₁)))) =
      -(∫ z, (fun z => ∑ i : Fin 3, ∑ j : Fin 3, D2u z i j j * φ z i) z ∂(volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁)))) := by
  let μ : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))
  have hu (i : Fin 3) : MemLp (fun z => u z i) 2 μ :=
    by simpa only [ContinuousLinearMap.proj_apply, μ] using
      huL2.continuousLinearMap_comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i)
  have hDu (i j : Fin 3) : MemLp (fun z => Du z i j) 2 μ := by
    let hproj : (Fin 3 → Vec3) →L[ℝ] Vec3 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Vec3) i :
        (Fin 3 → Vec3) →L[ℝ] Vec3)
    simpa [hproj, ContinuousLinearMap.proj_apply, μ] using
      (hDuL2.continuousLinearMap_comp hproj).continuousLinearMap_comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j)
  have hDtu (i : Fin 3) : MemLp (fun z => Dtu z i) 2 μ :=
    by simpa only [ContinuousLinearMap.proj_apply, μ] using
      hDtuL2.continuousLinearMap_comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i)
  have hD2 (i j k : Fin 3) : MemLp (fun z => D2u z i j k) 2 μ := by
    let hproj2 : (Fin 3 → Fin 3 → Vec3) →L[ℝ] (Fin 3 → Vec3) :=
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 3 => Fin 3 → Vec3) i :
        (Fin 3 → Fin 3 → Vec3) →L[ℝ] (Fin 3 → Vec3))
    let hproj3 : (Fin 3 → Vec3) →L[ℝ] Vec3 :=
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 3 => Vec3) j : (Fin 3 → Vec3) →L[ℝ] Vec3)
    have hfirst := hD2uL2.continuousLinearMap_comp hproj2
    have hsecond := hfirst.continuousLinearMap_comp hproj3
    have hthird := hsecond.continuousLinearMap_comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) k)
    simpa [hproj2, hproj3, ContinuousLinearMap.proj_apply, μ] using hthird
  have hcomponent (i : Fin 3) :=
    CKN.component_mem_spaceTimeTestFunction hφ i
  have hφL2 (i : Fin 3) : MemLp (fun z => φ z i) 2 μ :=
    (lps_spaceTimeTest_spatial_memLp_two (hcomponent i).1
      (hcomponent i).2.1 (Ioo t₀ t₁)).1
  have hφtimeL2 (i : Fin 3) :
      MemLp (fun z => timePartial (fun y => φ y i) z) 2 μ :=
    lps_spaceTimeTest_time_memLp_two (hcomponent i).1
      (hcomponent i).2.1 (Ioo t₀ t₁)
  have hφspaceL2 (i j : Fin 3) :
      MemLp (fun z => spatialPartial (fun y => φ y i) j z) 2 μ :=
    (lps_spaceTimeTest_spatial_memLp_two (hcomponent i).1
      (hcomponent i).2.1 (Ioo t₀ t₁)).2 j
  have htimeIBP (i : Fin 3) :=
    (hderivs.2.2.2.2 (fun z => φ z i) (hcomponent i)).2.2 i
  have hspaceIBP (i j : Fin 3) :=
    (hderivs.2.2.2.2 (fun z => φ z i) (hcomponent i)).2.1 i j j
  have htimeTerm (i : Fin 3) : Integrable
      (fun z => u z i * timePartial (fun y => φ y i) z) μ :=
    (hu i).integrable_mul (hφtimeL2 i)
  have htimeTarget (i : Fin 3) : Integrable
      (fun z => Dtu z i * φ z i) μ :=
    (hDtu i).integrable_mul (hφL2 i)
  have hdiffTerm (i j : Fin 3) : Integrable
      (fun z => Du z i j * spatialPartial (fun y => φ y i) j z) μ :=
    (hDu i j).integrable_mul (hφspaceL2 i j)
  have hdiffTarget (i j : Fin 3) : Integrable
      (fun z => D2u z i j j * φ z i) μ :=
    (hD2 i j j).integrable_mul (hφL2 i)
  have htimeIBPμ (i : Fin 3) :
      (∫ z, u z i * timePartial (fun y => φ y i) z ∂μ) =
        -(∫ z, Dtu z i * φ z i ∂μ) := by
    simpa [μ] using htimeIBP i
  have hspaceIBPμ (i j : Fin 3) :
      (∫ z, Du z i j * spatialPartial (fun y => φ y i) j z ∂μ) =
        -(∫ z, D2u z i j j * φ z i ∂μ) := by
    simpa [μ] using hspaceIBP i j
  have htimeSum : (∫ z, ∑ i : Fin 3,
      u z i * timePartial (fun y => φ y i) z ∂μ) =
      -(∫ z, ∑ i : Fin 3, Dtu z i * φ z i ∂μ) := by
    calc
      _ = ∑ i : Fin 3, ∫ z, u z i * timePartial (fun y => φ y i) z ∂μ :=
        integral_finsetSum _ (fun i _ => htimeTerm i)
      _ = ∑ i : Fin 3, -(∫ z, Dtu z i * φ z i ∂μ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact htimeIBPμ i
      _ = -(∑ i : Fin 3, ∫ z, Dtu z i * φ z i ∂μ) := by
        rw [Finset.sum_neg_distrib]
      _ = -(∫ z, ∑ i : Fin 3, Dtu z i * φ z i ∂μ) := by
        rw [integral_finsetSum _ (fun i _ => htimeTarget i)]
  have hdiffSum : (∫ z, ∑ i : Fin 3, ∑ j : Fin 3,
      Du z i j * spatialPartial (fun y => φ y i) j z ∂μ) =
      -(∫ z, ∑ i : Fin 3, ∑ j : Fin 3, D2u z i j j * φ z i ∂μ) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z, Du z i j * spatialPartial (fun y => φ y i) j z ∂μ := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hdiffTerm i j)]
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum _ (fun j _ => hdiffTerm i j)]
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          -(∫ z, D2u z i j j * φ z i ∂μ) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hspaceIBPμ i j
      _ = -(∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z, D2u z i j j * φ z i ∂μ) := by
        simp_rw [← Finset.sum_neg_distrib]
      _ = -(∫ z, ∑ i : Fin 3, ∑ j : Fin 3,
          D2u z i j j * φ z i ∂μ) := by
        have hdouble : (∫ z, ∑ i : Fin 3, ∑ j : Fin 3,
            D2u z i j j * φ z i ∂μ) =
            ∑ i : Fin 3, ∑ j : Fin 3,
              ∫ z, D2u z i j j * φ z i ∂μ := by
          calc
            _ = ∑ i : Fin 3, ∫ z, ∑ j : Fin 3,
                D2u z i j j * φ z i ∂μ :=
              integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hdiffTarget i j)
            _ = ∑ i : Fin 3, ∑ j : Fin 3,
                ∫ z, D2u z i j j * φ z i ∂μ := by
              apply Finset.sum_congr rfl
              intro i hi
              exact integral_finsetSum _ (fun j _ => hdiffTarget i j)
        exact congrArg Neg.neg hdouble.symm
  have htimeS : Integrable
      (fun z => ∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z) μ :=
    integrable_finsetSum _ fun i _ => htimeTerm i
  have htimeT : Integrable (fun z => ∑ i : Fin 3, Dtu z i * φ z i) μ :=
    integrable_finsetSum _ fun i _ => htimeTarget i
  have hdiffS : Integrable
      (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
        Du z i j * spatialPartial (fun y => φ y i) j z) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hdiffTerm i j
  have hdiffT : Integrable
      (fun z => ∑ i : Fin 3, ∑ j : Fin 3, D2u z i j j * φ z i) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hdiffTarget i j
  exact ⟨htimeS, htimeT, hdiffS, hdiffT, htimeSum, hdiffSum⟩

private lemma lps_nonlinear_pressure_test_integrals
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    (huL2 : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hpressure : MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (φ : ParabolicPoint → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Ioo t₀ t₁)) :
    Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * spatialPartial (fun y => φ y i) j z) (volume.restrict (spaceTimeSet
          (Set.univ : Set Vec3) (Ioo t₀ t₁))) ∧
    Integrable (fun z => p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))) := by
  let μ : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))
  have hu (i : Fin 3) : MemLp (fun z => u z i) 2 μ :=
    by simpa only [ContinuousLinearMap.proj_apply, μ] using
      huL2.continuousLinearMap_comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i)
  have hcomponent (i : Fin 3) :=
    CKN.component_mem_spaceTimeTestFunction hφ i
  have hφspaceL2 (i j : Fin 3) :
      MemLp (fun z => spatialPartial (fun y => φ y i) j z) 2 μ :=
    (lps_spaceTimeTest_spatial_memLp_two (hcomponent i).1
      (hcomponent i).2.1 (Ioo t₀ t₁)).2 j
  have hφdivL2 : MemLp
      (fun z => ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) 2 μ := by
    simpa only [Finset.sum_attach] using
      (memLp_finsetSum (Finset.univ : Finset (Fin 3))
        (fun i _ => hφspaceL2 i i))
  have hpressureTerm : Integrable
      (fun z => p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) μ :=
    hpressure.integrable_mul hφdivL2
  have hconvTerm (i j : Fin 3) : Integrable
      (fun z => u z i * u z j * spatialPartial (fun y => φ y i) j z) μ := by
    have hprod : Integrable (fun z => u z i * u z j) μ :=
      (hu i).integrable_mul (hu j)
    have hpartialCont : Continuous
        (fun z => spatialPartial (fun y => φ y i) j z) :=
      (CKN.spatialPartial_contDiff (hcomponent i).1 j).continuous
    have hpartialCpt : HasCompactSupport
        (fun z => spatialPartial (fun y => φ y i) j z) :=
      CKN.hasCompactSupport_spatialPartial (hcomponent i).2.1 j
    obtain ⟨C, hC⟩ := lps_continuous_compact_support_bounded_spaceTime
      hpartialCont hpartialCpt
    have hmul := hprod.mul_bdd (hφspaceL2 i j).aestronglyMeasurable
      (ae_of_all _ hC)
    exact hmul.congr (ae_of_all _ fun z => by ring)
  have hconvSum : Integrable
      (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * spatialPartial (fun y => φ y i) j z) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hconvTerm i j
  exact ⟨hconvSum, hpressureTerm⟩

/-- Integrating the strong weak equation by parts in time and space gives
its full pressure-inclusive distribution identity (`prop:lps-smoothing`).
The time derivative and Laplacian are the specified weak derivatives from
`IsLpsStrongSolution`. -/
theorem lps_strong_solution_full_weak_equation_D2
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsLpsStrongSolution t₀ t₁ u Du p)
    (φ : ParabolicPoint → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Ioo t₀ t₁)) :
    ∃ (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
      (Dtu : ParabolicPoint → Vec3),
      HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ t₁)
        u Du D2u Dtu ∧
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁),
        (∑ i : Fin 3, Dtu z i * φ z i
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          - ∑ i : Fin 3, ∑ j : Fin 3,
              D2u z i j j * φ z i
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) = 0 := by
  obtain ⟨hinterval, hslice, hcontinuous, hregularity, hpressure, hweak⟩ := hsol
  obtain ⟨D2u, Dtu, hderivs, huL2, hDuL2, hD2uL2, hDtuL2⟩ := hregularity
  obtain ⟨htimeS, htimeT, hdiffS, hdiffT, htimeSum, hdiffSum⟩ :=
    lps_weak_derivative_test_integrals hderivs huL2 hDuL2 hD2uL2 hDtuL2 φ hφ
  obtain ⟨hconvSum, hpressureTerm⟩ :=
    lps_nonlinear_pressure_test_integrals huL2 hpressure φ hφ
  refine ⟨D2u, Dtu, hderivs, ?_⟩
  exact lps_integral_weak_derivative_transfer htimeS htimeT hconvSum hdiffS hdiffT
    hpressureTerm htimeSum hdiffSum (hweak φ hφ)

/-- The complex Leray multiplier on frequency-space `L²` is linear. -/
@[expose] def lerayFourierMultiplierLinear :
    Lp (α := L2Vec3) ComplexVec3 2 →ₗ[ℂ]
      Lp (α := L2Vec3) ComplexVec3 2 where
  toFun := lerayFourierMultiplier
  map_add' f g := by
    change measurableFourierMultiplier
        (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
        lerayApplyFormula_measurable 1
        (by
          intro ξ z
          rw [← leraySymbol_apply_eq_formula]
          simpa using leraySymbol_norm_le ξ z) (f + g) =
      measurableFourierMultiplier
        (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
        lerayApplyFormula_measurable 1
        (by
          intro ξ z
          rw [← leraySymbol_apply_eq_formula]
          simpa using leraySymbol_norm_le ξ z) f +
      measurableFourierMultiplier
        (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
        lerayApplyFormula_measurable 1
        (by
          intro ξ z
          rw [← leraySymbol_apply_eq_formula]
          simpa using leraySymbol_norm_le ξ z) g
    apply Lp.ext
    have hf := measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
      lerayApplyFormula_measurable 1
      (by
        intro ξ z
        rw [← leraySymbol_apply_eq_formula]
        simpa using leraySymbol_norm_le ξ z) f
    have hg := measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
      lerayApplyFormula_measurable 1
      (by
        intro ξ z
        rw [← leraySymbol_apply_eq_formula]
        simpa using leraySymbol_norm_le ξ z) g
    have hfg := measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
      lerayApplyFormula_measurable 1
      (by
        intro ξ z
        rw [← leraySymbol_apply_eq_formula]
        simpa using leraySymbol_norm_le ξ z) (f + g)
    have hsumInput := Lp.coeFn_add f g
    have hsumOutput := Lp.coeFn_add
      (measurableFourierMultiplier
        (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
        lerayApplyFormula_measurable 1
        (by
          intro ξ z
          rw [← leraySymbol_apply_eq_formula]
          simpa using leraySymbol_norm_le ξ z) f)
      (measurableFourierMultiplier
        (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
        lerayApplyFormula_measurable 1
        (by
          intro ξ z
          rw [← leraySymbol_apply_eq_formula]
          simpa using leraySymbol_norm_le ξ z) g)
    filter_upwards [hf, hg, hfg, hsumInput, hsumOutput]
      with ξ hf hg hfg hsumInput hsumOutput
    rw [hfg, hsumInput, hsumOutput]
    simp only [Pi.add_apply, hf, hg]
    rw [← leraySymbol_apply_eq_formula ξ (f ξ + g ξ),
      ← leraySymbol_apply_eq_formula ξ (f ξ),
      ← leraySymbol_apply_eq_formula ξ (g ξ)]
    exact map_add (leraySymbol ξ) (f ξ) (g ξ)
  map_smul' c f := by
    change measurableFourierMultiplier
        (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
        lerayApplyFormula_measurable 1
        (by
          intro ξ z
          rw [← leraySymbol_apply_eq_formula]
          simpa using leraySymbol_norm_le ξ z) (c • f) =
      c • measurableFourierMultiplier
        (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
        lerayApplyFormula_measurable 1
        (by
          intro ξ z
          rw [← leraySymbol_apply_eq_formula]
          simpa using leraySymbol_norm_le ξ z) f
    apply Lp.ext
    have hf := measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
      lerayApplyFormula_measurable 1
      (by
        intro ξ z
        rw [← leraySymbol_apply_eq_formula]
        simpa using leraySymbol_norm_le ξ z) f
    have hcf := measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
      lerayApplyFormula_measurable 1
      (by
        intro ξ z
        rw [← leraySymbol_apply_eq_formula]
        simpa using leraySymbol_norm_le ξ z) (c • f)
    have hsmulInput := Lp.coeFn_smul c f
    have hsmulOutput := Lp.coeFn_smul c
      (measurableFourierMultiplier
        (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
        lerayApplyFormula_measurable 1
        (by
          intro ξ z
          rw [← leraySymbol_apply_eq_formula]
          simpa using leraySymbol_norm_le ξ z) f)
    filter_upwards [hf, hcf, hsmulInput, hsmulOutput]
      with ξ hf hcf hsmulInput hsmulOutput
    rw [hcf, hsmulInput, hsmulOutput]
    simp only [Pi.smul_apply, hf]
    rw [← leraySymbol_apply_eq_formula ξ (c • f ξ),
      ← leraySymbol_apply_eq_formula ξ (f ξ)]
    exact map_smul (leraySymbol ξ) c (f ξ)

/-- The complex physical-space Leray projection as a continuous linear map. -/
@[expose] def lerayProjectionL2CLM :
    ComplexVectorL2 →L[ℂ] ComplexVectorL2 := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  let A : Lp (α := L2Vec3) ComplexVec3 2 →ₗ[ℂ]
      Lp (α := L2Vec3) ComplexVec3 2 := ℱ.symm.toLinearEquiv.toLinearMap.comp
        (lerayFourierMultiplierLinear.comp ℱ.toLinearEquiv.toLinearMap)
  exact A.mkContinuous 1 (by
    intro f
    change ‖lerayProjectionL2 f‖ ≤ 1 * ‖f‖
    simpa [lerayProjectionL2] using lerayProjectionL2_norm_le f)

/-- The real Leray projection is a continuous linear map on spatial `L²`. -/
@[expose] def realLerayProjectionCLM : RealVectorL2 →L[ℝ] RealVectorL2 :=
  realPartVectorL2.comp
    ((lerayProjectionL2CLM.restrictScalars ℝ).comp complexifyVectorL2)

/-- The continuous linear realization agrees with the real Leray projection
used in the Fourier construction. -/
theorem realLerayProjectionCLM_apply (f : RealVectorL2) :
    realLerayProjectionCLM f = realLerayProjection f := by
  change realPartVectorL2 (lerayProjectionL2CLM (complexifyVectorL2 f)) = _
  rfl

/-- The real Leray projection contracts the spatial `L²` norm. -/
theorem realLerayProjectionCLM_norm_le (f : RealVectorL2) :
    ‖realLerayProjectionCLM f‖ ≤ ‖f‖ := by
  rw [realLerayProjectionCLM_apply]
  exact realLerayProjection_norm_le f

/-- The Leray projection fixes every spatial `L²` field whose representative
is weakly divergence-free (`prop:lps-smoothing`). -/
theorem realLerayProjectionCLM_eq_self_of_isWeakDivFree
    (f : RealVectorL2)
    (hf : CKN.IsWeakDivFreeL2 (realVectorL2Representative f)) :
    realLerayProjectionCLM f = f := by
  let Pf := realLerayProjectionCLM f
  have hPdiv : CKN.IsWeakDivFreeL2 (realVectorL2Representative Pf) := by
    rw [show Pf = realLerayProjection f from realLerayProjectionCLM_apply f]
    exact realLerayProjection_isWeakDivFree f
  have h1 := realLerayProjection_inner_of_isWeakDivFree f f hf
  have h2 := realLerayProjection_inner_of_isWeakDivFree f Pf hPdiv
  have hPf : Pf = realLerayProjection f :=
    realLerayProjectionCLM_apply f
  have h1P : inner ℝ Pf f = inner ℝ f f := by
    rw [hPf]
    exact h1
  have h2P : inner ℝ Pf Pf = inner ℝ f Pf := by
    rw [hPf]
    exact h2
  have hinner : inner ℝ (Pf - f) (Pf - f) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    rw [h2P, h1P]
    ring
  have hdiff : ‖Pf - f‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hinner
  have hzero : ‖Pf - f‖ = 0 := (sq_eq_zero_iff).mp hdiff
  have : Pf - f = 0 := norm_eq_zero.mp hzero
  dsimp [Pf] at this
  exact sub_eq_zero.mp this

/-- Every strong-solution time slice is fixed by the Leray projection in
spatial `L²` (`prop:lps-smoothing`). -/
theorem lps_strong_solution_slice_projection_eq
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsLpsStrongSolution t₀ t₁ u Du p)
    {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    let hSlice : MemLp (fun x : Vec3 => u (x, t)) 2 volume :=
      (hsol.2.1 t ht).1.1
    realLerayProjectionCLM
        (realVectorL2OfCoordinateFunction (fun x => u (x, t)) hSlice) =
      realVectorL2OfCoordinateFunction (fun x => u (x, t)) hSlice := by
  dsimp
  let hJ := (hsol.2.1 t ht).1
  let hSlice : MemLp (fun x : Vec3 => u (x, t)) 2 volume := hJ.1
  let f : RealVectorL2 := realVectorL2OfCoordinateFunction
    (fun x => u (x, t)) hSlice
  have hdivU : CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)) :=
    (CKN.isInJ_iff_weakDivFree).1 hJ
  have hrep : realVectorL2Representative f =ᵐ[volume]
      (fun x : Vec3 => u (x, t)) :=
    realVectorL2OfCoordinateFunction_rep _ hSlice
  have hdivF : CKN.IsWeakDivFreeL2 (realVectorL2Representative f) :=
    isWeakDivFree_congr_ae hrep.symm hdivU
  have hfixed := realLerayProjectionCLM_eq_self_of_isWeakDivFree f hdivF
  simpa [f, hSlice] using hfixed

/-- Applying the Leray projection in each ordered derivative slot does not
increase the finite `H^m` sum of spatial `L²` norms (`prop:lps-smoothing`).
Identifying these slots with the weak derivatives of the projected field is
the separate distributional commutation step. -/
theorem realLerayProjection_orderedL2_energy_le
    (m : ℕ) (F : List (Fin 3) → RealVectorL2) :
    ∑ α ∈ sobolevWords m, ‖realLerayProjectionCLM (F α)‖ ^ 2 ≤
      ∑ α ∈ sobolevWords m, ‖F α‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro α hα
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (realLerayProjectionCLM_norm_le (F α))

/-- The finite product of spatial `L²` slots through ordered derivative
degree `m`. -/
abbrev OrderedSpatialL2Family (m : ℕ) :=
  PiLp 2 (fun _ : {α : List (Fin 3) // α ∈ sobolevWords m} => RealVectorL2)

/-- Apply the Leray multiplier in each ordered spatial `L²` slot through
degree `m`. -/
@[expose] def realLerayProjectionOrderedLinear (m : ℕ) :
    OrderedSpatialL2Family m →ₗ[ℝ] OrderedSpatialL2Family m where
  toFun F := WithLp.toLp 2 (fun α => realLerayProjectionCLM (F α))
  map_add' F G := by
    apply PiLp.ext
    intro α
    exact map_add realLerayProjectionCLM (F α) (G α)
  map_smul' c F := by
    apply PiLp.ext
    intro α
    exact map_smul realLerayProjectionCLM c (F α)

/-- The Leray multiplier is a contraction on the finite ordered integer
`H^m` product of spatial `L²` slots (`prop:lps-smoothing`). This bound is the
operator estimate used after identifying the projected slots with weak
derivatives. -/
@[expose] def realLerayProjectionOrderedCLM (m : ℕ) :
    OrderedSpatialL2Family m →L[ℝ] OrderedSpatialL2Family m := by
  let A := realLerayProjectionOrderedLinear m
  refine A.mkContinuous 1 ?_
  intro F
  change ‖WithLp.toLp 2 (fun α => realLerayProjectionCLM (F α))‖ ≤
    1 * ‖F‖
  rw [one_mul, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro α hα
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (realLerayProjectionCLM_norm_le (F α))

/-- The ordered Sobolev multiplier is linear slotwise. -/
theorem realLerayProjectionOrderedCLM_apply
    (m : ℕ) (F : OrderedSpatialL2Family m)
    (α : {α : List (Fin 3) // α ∈ sobolevWords m}) :
    realLerayProjectionOrderedCLM m F α =
      realLerayProjectionCLM (F α) := by
  rfl

/-- The Leray multiplier does not increase the ordered integer `H^m` norm
(`prop:lps-smoothing`). -/
theorem realLerayProjectionOrderedCLM_norm_le
    (m : ℕ) (F : OrderedSpatialL2Family m) :
    ‖realLerayProjectionOrderedCLM m F‖ ≤ ‖F‖ := by
  change ‖WithLp.toLp 2 (fun α => realLerayProjectionCLM (F α))‖ ≤ ‖F‖
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro α hα
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (realLerayProjectionCLM_norm_le (F α))

end ESS.LPS

end

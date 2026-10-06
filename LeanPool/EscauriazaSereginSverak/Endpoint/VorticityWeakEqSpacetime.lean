/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityConvection
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTestCalculus
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.CompactLp
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Space-time weak vorticity equation

Compact tests are localized to CKN local boxes, where the suitable solution
provides almost-everywhere spatial weak gradients.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic

namespace ESS

/-- A compactly supported integrand has the same integral over any set that
contains its support and over its support (manuscript
`lem:vorticity-weak-eq`). -/
theorem integralOn_eq_of_subset_of_zero_off
    {S K : Set ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hKS : K ⊆ S) (hf : ∀ z, z ∉ K → f z = 0) :
    (∫ z in S, f z) = ∫ z in K, f z := by
  have hS : (∫ z in S, f z) = ∫ z, f z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hf z (fun hK => hz (hKS hK))
  have hK : (∫ z in K, f z) = ∫ z, f z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    exact hf
  exact hS.trans hK.symm

private theorem suitableWeakVelocityTestIntegrableOnSupport
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0))
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) Ω I) (i : Fin 3) :
    IntegrableOn (fun z : ParabolicPoint => u z i * φ z)
      (tsupport (show ParabolicPoint → ℝ from φ)) volume := by
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → ℝ from φ)
  have hK : IsCompact K := CKN.isCompact_tsupport_parabolic hφ.2.1
  have hKsub : K ⊆ CKN.spaceTimeSet Ω I :=
    CKN.tsupport_parabolic_subset_spaceTimeSet hφ
  obtain ⟨C, hC⟩ := CKN.exists_bound_of_mem_spaceTimeTestFunction hφ
  exact (CKN.velocity_component_integrableOn_compact_of_data hdata hK hKsub i).mul_bdd
    (c := C) (g := fun z : ParabolicPoint => φ z)
    hφ.1.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)

private theorem suitableWeakGradientTestIntegrableOnSupport
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0))
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) Ω I)
    (i j : Fin 3) :
    IntegrableOn (fun z : ParabolicPoint => Du z i j * φ z)
      (tsupport (show ParabolicPoint → ℝ from φ)) volume := by
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → ℝ from φ)
  have hK : IsCompact K := CKN.isCompact_tsupport_parabolic hφ.2.1
  have hKsub : K ⊆ CKN.spaceTimeSet Ω I :=
    CKN.tsupport_parabolic_subset_spaceTimeSet hφ
  obtain ⟨C, hC⟩ := CKN.exists_bound_of_mem_spaceTimeTestFunction hφ
  exact (CKN.gradient_entry_integrableOn_compact_of_data hdata hK hKsub i j).mul_bdd
    (c := C) (g := fun z : ParabolicPoint => φ z)
    hφ.1.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)

private theorem vorticityScalarComponentTest
    {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I) (i : Fin 3) :
    (fun z : Vec3 × ℝ => ψ z i) ∈ CKN.spaceTimeTestFunction (V := ℝ) Ω I :=
  CKN.component_mem_spaceTimeTestFunction hψ i

/-- A CKN scalar test remains a test after taking a spatial derivative. -/
theorem vorticitySpatialPartialTest
    {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) Ω I) (j : Fin 3) :
    (fun z : Vec3 × ℝ => CKN.spatialPartial φ j z) ∈
      CKN.spaceTimeTestFunction (V := ℝ) Ω I := by
  refine ⟨CKN.spatialPartial_contDiff hφ.1 j,
    CKN.hasCompactSupport_spatialPartial hφ.2.1 j, ?_⟩
  exact (CKN.tsupport_spatialPartial_subset j).trans hφ.2.2

/-- A CKN scalar test remains a test after time differentiation. -/
theorem vorticityTimePartialTest
    {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) Ω I) :
    (fun z : Vec3 × ℝ => CKN.timePartial φ z) ∈
      CKN.spaceTimeTestFunction (V := ℝ) Ω I := by
  refine ⟨CKN.contDiff_timePartial hφ.1,
    CKN.hasCompactSupport_timePartial hφ.2.1, ?_⟩
  exact (CKN.tsupport_timePartial_subset φ).trans hφ.2.2

/-- The space-time set of a CKN local box is null-measurable for the
parabolic volume measure (manuscript `lem:vorticity-weak-eq`). -/
theorem localBox_spaceTimeSet_nullMeasurable
    {Ω : Set Vec3} {I : Set ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : CKN.localBox Ω I Ω' J) :
    NullMeasurableSet (CKN.spaceTimeSet Ω' J) volume := by
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  change NullMeasurableSet (Ω' ×ˢ J)
    ((volume : Measure Vec3).prod (volume : Measure ℝ))
  exact hbox.1.measurableSet.nullMeasurableSet.prod
    hbox.2.2.2.1.measurableSet.nullMeasurableSet

/-- Suitable velocity components multiplied by a compact test are integrable
on every local box (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakVelocityTestIntegrableOnBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0))
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : CKN.localBox Ω I Ω' J)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) Ω I)
    (i : Fin 3) :
    IntegrableOn (fun z : ParabolicPoint => u z i * φ z)
      (CKN.spaceTimeSet Ω' J) volume := by
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → ℝ from φ)
  have hKint := suitableWeakVelocityTestIntegrableOnSupport hdata hφ i
  have hzero (z : ParabolicPoint) (hz : z ∉ K) : u z i * φ z = 0 := by
    have hzprod : (show Vec3 × ℝ from z) ∉ tsupport φ := by
      intro hφz
      apply hz
      change z ∈ tsupport (show ParabolicPoint → ℝ from φ)
      rw [CKN.tsupport_parabolic_eq]
      exact hφz
    have hφz := image_eq_zero_of_notMem_tsupport hzprod
    simp [hφz]
  apply hKint.of_ae_sdiff_eq_zero (localBox_spaceTimeSet_nullMeasurable hbox)
  filter_upwards [] with z hz
  exact hzero z hz.2

/-- Suitable weak-gradient components multiplied by a compact test are
integrable on every local box (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakGradientTestIntegrableOnBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hdata : CKN.IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0))
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : CKN.localBox Ω I Ω' J)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) Ω I)
    (i j : Fin 3) :
    IntegrableOn (fun z : ParabolicPoint => Du z i j * φ z)
      (CKN.spaceTimeSet Ω' J) volume := by
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → ℝ from φ)
  have hKint := suitableWeakGradientTestIntegrableOnSupport hdata hφ i j
  have hzero (z : ParabolicPoint) (hz : z ∉ K) : Du z i j * φ z = 0 := by
    have hzprod : (show Vec3 × ℝ from z) ∉ tsupport φ := by
      intro hφz
      apply hz
      change z ∈ tsupport (show ParabolicPoint → ℝ from φ)
      rw [CKN.tsupport_parabolic_eq]
      exact hφz
    have hφz := image_eq_zero_of_notMem_tsupport hzprod
    simp [hφz]
  apply hKint.of_ae_sdiff_eq_zero (localBox_spaceTimeSet_nullMeasurable hbox)
  filter_upwards [] with z hz
  exact hzero z hz.2

/-- Fubini's theorem in the native parabolic carrier identifies a local
space-time integral with its time-first iterated integral. -/
theorem vorticity_integral_on_box_eq_iterated
    {Ω' : Set Vec3} {J : Set ℝ} {f : ParabolicPoint → ℝ}
    (hf : IntegrableOn f (CKN.spaceTimeSet Ω' J) volume) :
    (∫ z in CKN.spaceTimeSet Ω' J, f z) =
      ∫ t in J, ∫ x in Ω', f (x, t) := by
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  change (∫ z in Ω' ×ˢ J, f z
      ∂((volume : Measure Vec3).prod (volume : Measure ℝ))) = _
  have hswap : IntegrableOn (fun z : ℝ × Vec3 => f z.swap)
      (J ×ˢ Ω') ((volume : Measure ℝ).prod (volume : Measure Vec3)) := hf.swap
  calc
    (∫ z in Ω' ×ˢ J, f z
        ∂((volume : Measure Vec3).prod (volume : Measure ℝ))) =
      ∫ z in J ×ˢ Ω', f z.swap
        ∂((volume : Measure ℝ).prod (volume : Measure Vec3)) :=
      (setIntegral_prod_swap (μ := (volume : Measure Vec3))
        (ν := (volume : Measure ℝ)) Ω' J f).symm
    _ = ∫ t in J, ∫ x in Ω', f (x, t) := by
      rw [setIntegral_prod _ hswap]
      rfl

/-- Testing the suitable momentum equation with the curl of a compact test
field removes the pressure and zero force terms (manuscript
`lem:vorticity-weak-eq`). -/
theorem suitableWeakMomentumTestCurl
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (h : CKN.IsSuitableWeakSolution Ω I q u Du p (fun _ => 0))
    {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I) :
    ∫ z in CKN.spaceTimeSet Ω I,
      (-(∑ i : Fin 3, u z i * CKN.timePartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * CKN.spatialPartial
              (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * CKN.spatialPartial
              (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z = 0 := by
  have hInt : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ => 0) :=
    CKN.isSuitableWeakSolution_iff_integrable.mp h
  rcases hInt with ⟨_, _, _, _, _, _, _, hmom, _⟩
  have hcurl : vorticityTestCurl ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I :=
    vorticityTestCurl_mem_spaceTimeTestFunction hψ
  have hdiv := vorticityTestCurl_divergence hψ.1
  have hdiv' (z : ParabolicPoint) :
      ∑ i : Fin 3, CKN.spatialPartial
        (fun w : ParabolicPoint => vorticityTestCurl ψ w i) i z = 0 := by
    have hz := hdiv (show Vec3 × ℝ from z)
    calc
      _ = ∑ i : Fin 3, vorticityTestPartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) i
          (show Vec3 × ℝ from z) := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = 0 := hz
  have hmomentum := hmom (vorticityTestCurl ψ) hcurl
  have hpoint (z : ParabolicPoint) :
      (-(∑ i : Fin 3, u z i * CKN.timePartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * CKN.spatialPartial
              (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * CKN.spatialPartial
              (fun w : ParabolicPoint => vorticityTestCurl ψ w i) j z =
      (-(∑ i : Fin 3, u z i * CKN.timePartial
          (fun w : ParabolicPoint => vorticityTestCurl ψ w i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * CKN.spatialPartial
              (fun w : ParabolicPoint => vorticityTestCurl ψ w i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * CKN.spatialPartial
              (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z
        - p z * ∑ i : Fin 3, CKN.spatialPartial
            (fun w : ParabolicPoint => vorticityTestCurl ψ w i) i z
        - ∑ i : Fin 3, (0 : ℝ) * vorticityTestCurl ψ z i := by
    rw [hdiv' z]
    simp
    rfl
  calc
    ∫ z in CKN.spaceTimeSet Ω I,
      (-(∑ i : Fin 3, u z i * CKN.timePartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * CKN.spatialPartial
                (fun w : ParabolicPoint => vorticityTestCurl ψ w i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * CKN.spatialPartial
                (fun w : ParabolicPoint => vorticityTestCurl ψ w i) j z
        = ∫ z in CKN.spaceTimeSet Ω I,
          (-(∑ i : Fin 3, u z i * CKN.timePartial
              (fun w : ParabolicPoint => vorticityTestCurl ψ w i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * CKN.spatialPartial
                  (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * CKN.spatialPartial
                  (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z
            - p z * ∑ i : Fin 3, CKN.spatialPartial
                (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) i z
            - ∑ i : Fin 3, (0 : ℝ) * vorticityTestCurl ψ z i :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = 0 := hmomentum.2

/-- The curl-tested momentum identity can be restricted to the compact support
of the test curl (manuscript `lem:vorticity-weak-eq`). -/
theorem suitableWeakMomentumTestCurlOnSupport
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (h : CKN.IsSuitableWeakSolution Ω I q u Du p (fun _ => 0))
    {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I) :
    ∫ z in tsupport (show ParabolicPoint → Vec3 from vorticityTestCurl ψ),
      (-(∑ i : Fin 3, u z i * CKN.timePartial
          (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * CKN.spatialPartial
              (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * CKN.spatialPartial
              (fun w : Vec3 × ℝ => vorticityTestCurl ψ w i) j z = 0 := by
  let χ : Vec3 × ℝ → Vec3 := vorticityTestCurl ψ
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → Vec3 from χ)
  have hχ : χ ∈ CKN.spaceTimeTestFunction (V := Vec3) Ω I := by
    exact vorticityTestCurl_mem_spaceTimeTestFunction hψ
  have hKsub : K ⊆ CKN.spaceTimeSet Ω I := by
    dsimp [K]
    exact CKN.tsupport_parabolic_subset_spaceTimeSet hχ
  have hzero (z : ParabolicPoint) (hz : z ∉ K) :
      (-(∑ i : Fin 3, u z i * CKN.timePartial
          (fun w : Vec3 × ℝ => χ w i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * CKN.spatialPartial
              (fun w : Vec3 × ℝ => χ w i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * CKN.spatialPartial
              (fun w : Vec3 × ℝ => χ w i) j z = 0 := by
    have hzprod : (show Vec3 × ℝ from z) ∉ tsupport χ := by
      intro hzχ
      apply hz
      change z ∈ tsupport (show ParabolicPoint → Vec3 from χ)
      rw [CKN.tsupport_parabolic_eq]
      exact hzχ
    have hcompsub (i : Fin 3) :
        tsupport (fun w : Vec3 × ℝ => χ w i) ⊆ tsupport χ :=
      CKN.tsupport_component_subset (V := Vec3) (ι := Fin 3) χ i
        (by intro w hw; simp [hw])
    have hnot (i : Fin 3) :
        (show Vec3 × ℝ from z) ∉ tsupport (fun w : Vec3 × ℝ => χ w i) :=
      fun hi => hzprod (hcompsub i hi)
    have htime (i : Fin 3) :
        CKN.timePartial (fun w : Vec3 × ℝ => χ w i) z = 0 := by
      change CKN.timePartial (fun w : Vec3 × ℝ => χ w i)
        (show Vec3 × ℝ from z) = 0
      exact CKN.timePartial_eq_zero_off_tsupport (hnot i)
    have hspace (i j : Fin 3) :
        CKN.spatialPartial (fun w : Vec3 × ℝ => χ w i) j z = 0 := by
      change CKN.spatialPartial (fun w : Vec3 × ℝ => χ w i) j
        (show Vec3 × ℝ from z) = 0
      exact CKN.spatialPartial_eq_zero_off_tsupport (hnot i) j
    simp [htime, hspace]
  have heq := integralOn_eq_of_subset_of_zero_off hKsub hzero
  rw [← heq]
  simpa [χ, K] using suitableWeakMomentumTestCurl h hψ

end ESS

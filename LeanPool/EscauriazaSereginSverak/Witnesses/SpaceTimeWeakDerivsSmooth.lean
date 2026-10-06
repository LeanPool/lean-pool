/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.FactorIBP
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Doubling
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs

/-!
# Smooth fields have space-time weak derivatives

The classical spatial and time derivatives of a smooth field satisfy the
space-time integration-by-parts definition in `def:sws`.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

@[expose] def classicalSpatialDerivative (w : ParabolicPoint → Vec3) :
    ParabolicPoint → Fin 3 → Vec3 :=
  fun z i j => spatialPartial (fun y => w y i) j z

@[expose] def classicalSpatialSecondDerivative (w : ParabolicPoint → Vec3) :
    ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
  fun z i j k => spatialPartial (fun y => spatialPartial (fun x => w x i) j y) k z

@[expose] def classicalTimeDerivative (w : ParabolicPoint → Vec3) :
    ParabolicPoint → Vec3 :=
  fun z i => timePartial (fun y => w y i) z

private instance parabolicVolumeIsLocallyFinite :
    IsLocallyFiniteMeasure (volume : Measure ParabolicPoint) :=
  ⟨fun z => ⟨Metric.ball z 1, Metric.ball_mem_nhds z one_pos,
    CKN.Foundation.Parabolic.volume_parabolicBall_lt_top one_pos⟩⟩



/-- A smooth field has its classical first, second, and time derivatives as
space-time weak derivatives on every open product domain. -/
theorem hasSpaceTimeWeakDerivs_of_contDiff
    {Ω : Set Vec3} {I : Set ℝ} {w : ParabolicPoint → Vec3}
    (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hw : ContDiff ℝ (⊤ : ℕ∞) (show Vec3 × ℝ → Vec3 from w)) :
    HasSpaceTimeWeakDerivs Ω I w
      (fun z i j => spatialPartial (fun y => w y i) j z)
      (fun z i j k => spatialPartial (fun y => spatialPartial (fun x => w x i) j y) k z)
      (fun z i => timePartial (fun y => w y i) z) := by
  let K : Set ParabolicPoint := spaceTimeSet Ω I
  have hK : MeasurableSet K :=
    (CKN.Foundation.Parabolic.isOpen_spaceTimeSet Ω I hΩ hI).measurableSet
  have hcomponent (i : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => w z i) :=
    CKN.component_contDiff (show ContDiff ℝ (⊤ : ℕ∞) (show Vec3 × ℝ → Vec3 from w)
      from hw) i
  have hfirst (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ => spatialPartial (fun y => w y i) j z) :=
    CKN.spatialPartial_contDiff (hcomponent i) j
  have hsecond (i j k : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ =>
          spatialPartial (fun y => spatialPartial (fun x => w x i) j y) k z) :=
    CKN.spatialPartial_contDiff (hfirst i j) k
  have htime (i : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ => timePartial (fun y => w y i) z) :=
    CKN.timePartial_contDiff (hcomponent i)
  have hfirstContinuousProd : Continuous
      (fun z : Vec3 × ℝ => fun i : Fin 3 => fun j : Fin 3 =>
        spatialPartial (fun y => w y i) j z) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (hfirst i j).continuous
  have hsecondContinuousProd : Continuous
      (fun z : Vec3 × ℝ => fun i : Fin 3 => fun j : Fin 3 => fun k : Fin 3 =>
        spatialPartial (fun y => spatialPartial (fun x => w x i) j y) k z) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply continuous_pi
    intro k
    exact (hsecond i j k).continuous
  have htimeContinuousProd : Continuous
      (fun z : Vec3 × ℝ => fun i : Fin 3 => timePartial (fun y => w y i) z) := by
    apply continuous_pi
    intro i
    exact (htime i).continuous
  have hfirstContinuous : Continuous (classicalSpatialDerivative w) := by
    change Continuous
      ((fun z : Vec3 × ℝ => fun i : Fin 3 => fun j : Fin 3 =>
        spatialPartial (fun y => w y i) j z) ∘ parabolicHomeomorph)
    exact hfirstContinuousProd.comp parabolicHomeomorph.continuous
  have hsecondContinuous : Continuous (classicalSpatialSecondDerivative w) := by
    change Continuous
      ((fun z : Vec3 × ℝ => fun i : Fin 3 => fun j : Fin 3 => fun k : Fin 3 =>
        spatialPartial (fun y => spatialPartial (fun x => w x i) j y) k z) ∘
          parabolicHomeomorph)
    exact hsecondContinuousProd.comp parabolicHomeomorph.continuous
  have htimeContinuous : Continuous (classicalTimeDerivative w) := by
    change Continuous
      ((fun z : Vec3 × ℝ => fun i : Fin 3 => timePartial (fun y => w y i) z) ∘
        parabolicHomeomorph)
    exact htimeContinuousProd.comp parabolicHomeomorph.continuous
  have hwContinuous : Continuous
      (show ParabolicPoint → Vec3 from fun z =>
        (show Vec3 × ℝ → Vec3 from w) (parabolicHomeomorph z)) :=
    hw.continuous.comp parabolicHomeomorph.continuous
  have hwField : (show ParabolicPoint → Vec3 from
      fun z => (show Vec3 × ℝ → Vec3 from w) (parabolicHomeomorph z)) = w := by
    funext z
    rfl
  have hwLoc : LocallyIntegrableOn w K volume := by
    rw [← hwField]
    exact hwContinuous.locallyIntegrable.locallyIntegrableOn K
  refine ⟨hwLoc,
    hfirstContinuous.locallyIntegrable.locallyIntegrableOn K,
    hsecondContinuous.locallyIntegrable.locallyIntegrableOn K,
    htimeContinuous.locallyIntegrable.locallyIntegrableOn K, ?_⟩
  intro φ hφ
  rcases hφ with ⟨hφdiff, hφcompact, hφsupport⟩
  have hφsupportPar :
      tsupport (show ParabolicPoint → ℝ from φ) ⊆ K := by
    rw [CKN.tsupport_parabolic_eq (show Vec3 × ℝ → ℝ from φ)]
    exact hφsupport
  have hvolume : (volume : Measure ParabolicPoint) = (volume : Measure (Vec3 × ℝ)) := by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod,
      Measure.volume_eq_prod Vec3 ℝ]
  have htestSupport (j : Fin 3) :
      tsupport (fun z : ParabolicPoint => spatialPartial φ j z) ⊆ K := by
    let dφ : Vec3 × ℝ → ℝ := fun z =>
      spatialPartial (show ParabolicPoint → ℝ from φ) j (parabolicHomeomorph.symm z)
    have hdφ : dφ = fun z : Vec3 × ℝ => spatialPartial φ j z := by
      funext z
      simp [dφ]
    have hdφSupport : tsupport dφ ⊆ tsupport (show Vec3 × ℝ → ℝ from φ) := by
      rw [hdφ]
      exact CKN.tsupport_spatialPartial_subset
        (ψ := show Vec3 × ℝ → ℝ from φ) j
    have hparEq : (show ParabolicPoint → ℝ from dφ) =
        (fun z : ParabolicPoint => spatialPartial φ j z) := by
      funext z
      simp [dφ]
    rw [← hparEq, CKN.tsupport_parabolic_eq dφ]
    exact hdφSupport.trans hφsupport
  have hfirstIdentity : ∀ i j : Fin 3,
      ∫ z in K, w z i * spatialPartial φ j z =
        -∫ z in K, classicalSpatialDerivative w z i j * φ z := by
    intro i j
    have hleftSupport :
        tsupport (fun z : ParabolicPoint => w z i * spatialPartial φ j z) ⊆ K := by
      exact (tsupport_mul_subset_right (f := fun z : ParabolicPoint => w z i)
        (g := fun z => spatialPartial φ j z)).trans (htestSupport j)
    have hrightSupport :
        tsupport (fun z : ParabolicPoint =>
          spatialPartial (fun y => w y i) j z * φ z) ⊆ K := by
      exact (tsupport_mul_subset_right
        (f := fun z : ParabolicPoint => spatialPartial (fun y => w y i) j z)
        (g := φ)).trans hφsupportPar
    have hIBP := CKN.integral_mul_spatialPartial_eq_neg_spatialPartial_mul
      (hcomponent i) hφdiff hφcompact j
    simp only [classicalSpatialDerivative]
    rw [CKN.setIntegral_eq_integral_of_tsupport_subset hK hleftSupport,
      CKN.setIntegral_eq_integral_of_tsupport_subset hK hrightSupport, hvolume]
    exact hIBP
  have hsecondIdentity : ∀ i j k : Fin 3,
      ∫ z in K, classicalSpatialDerivative w z i j * spatialPartial φ k z =
        -∫ z in K, classicalSpatialSecondDerivative w z i j k * φ z := by
    intro i j k
    have hleftSupport :
        tsupport (fun z : ParabolicPoint =>
          classicalSpatialDerivative w z i j * spatialPartial φ k z) ⊆ K := by
      exact (tsupport_mul_subset_right
        (f := fun z : ParabolicPoint => classicalSpatialDerivative w z i j)
        (g := fun z => spatialPartial φ k z)).trans (htestSupport k)
    have hrightSupport :
        tsupport (fun z : ParabolicPoint =>
          classicalSpatialSecondDerivative w z i j k * φ z) ⊆ K := by
      exact (tsupport_mul_subset_right
        (f := fun z : ParabolicPoint => classicalSpatialSecondDerivative w z i j k)
        (g := φ)).trans hφsupportPar
    have hIBP := CKN.integral_mul_spatialPartial_eq_neg_spatialPartial_mul
      (hfirst i j) hφdiff hφcompact k
    simp only [classicalSpatialDerivative, classicalSpatialSecondDerivative]
    change tsupport (fun z : ParabolicPoint =>
      spatialPartial (fun y => w y i) j z * spatialPartial φ k z) ⊆ K at hleftSupport
    change tsupport (fun z : ParabolicPoint =>
      spatialPartial (fun y => spatialPartial (fun x => w x i) j y) k z * φ z) ⊆ K
      at hrightSupport
    rw [CKN.setIntegral_eq_integral_of_tsupport_subset hK hleftSupport,
      CKN.setIntegral_eq_integral_of_tsupport_subset hK hrightSupport, hvolume]
    exact hIBP
  have htimeIdentity : ∀ i : Fin 3,
      ∫ z in K, w z i * timePartial φ z =
        -∫ z in K, classicalTimeDerivative w z i * φ z := by
    intro i
    let dφ : Vec3 × ℝ → ℝ := fun z =>
      timePartial (show ParabolicPoint → ℝ from φ) (parabolicHomeomorph.symm z)
    have hdφ : dφ = fun z : Vec3 × ℝ => timePartial φ z := by
      funext z
      simp [dφ]
    have hdφSupport : tsupport dφ ⊆ tsupport (show Vec3 × ℝ → ℝ from φ) := by
      rw [hdφ]
      exact CKN.tsupport_timePartial_subset φ
    have hparEq : (show ParabolicPoint → ℝ from dφ) =
        (fun z : ParabolicPoint => timePartial φ z) := by
      funext z
      simp [dφ]
    have htestSupport :
        tsupport (fun z : ParabolicPoint => timePartial φ z) ⊆ K := by
      rw [← hparEq, CKN.tsupport_parabolic_eq dφ]
      exact hdφSupport.trans hφsupport
    have hleftSupport :
        tsupport (fun z : ParabolicPoint => w z i * timePartial φ z) ⊆ K := by
      exact (tsupport_mul_subset_right (f := fun z : ParabolicPoint => w z i)
        (g := fun z => timePartial φ z)).trans htestSupport
    have hrightSupport :
        tsupport (fun z : ParabolicPoint => classicalTimeDerivative w z i * φ z) ⊆ K := by
      exact (tsupport_mul_subset_right
        (f := fun z : ParabolicPoint => classicalTimeDerivative w z i)
        (g := φ)).trans hφsupportPar
    have hIBP := CKN.integral_mul_timePartial_eq_neg_timePartial_mul
      (hcomponent i) hφdiff hφcompact
    simp only [classicalTimeDerivative]
    change tsupport (fun z : ParabolicPoint =>
      timePartial (fun y => w y i) z * φ z) ⊆ K at hrightSupport
    rw [CKN.setIntegral_eq_integral_of_tsupport_subset hK hleftSupport,
      CKN.setIntegral_eq_integral_of_tsupport_subset hK hrightSupport, hvolume]
    exact hIBP
  exact ⟨hfirstIdentity, hsecondIdentity, htimeIdentity⟩

/-- The constant nonzero field has classical space-time weak derivatives,
which all vanish. -/
theorem hasSpaceTimeWeakDerivs_nonzero_witness
    (Ω : Set Vec3) (I : Set ℝ) (hΩ : IsOpen Ω) (hI : IsOpen I) :
    (fun _ : ParabolicPoint => fun _ : Fin 3 => (1 : ℝ)) ((0 : Vec3), 0) 0 ≠ 0 ∧
      HasSpaceTimeWeakDerivs Ω I (fun _ : ParabolicPoint => fun _ : Fin 3 => (1 : ℝ))
        (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  constructor
  · norm_num
  · let w : ParabolicPoint → Vec3 := fun _ => fun _ => (1 : ℝ)
    have hconstant :
        ContDiff ℝ (⊤ : ℕ∞) (show Vec3 × ℝ → Vec3 from w) := contDiff_const
    have hweak := hasSpaceTimeWeakDerivs_of_contDiff hΩ hI hconstant
    have hfirst :
        (fun z i j => spatialPartial (fun y => w y i) j z) = fun _ => 0 := by
      funext z i j
      simp [w, spatialPartial]
    have hsecond :
        (fun z i j k =>
          spatialPartial (fun y => spatialPartial (fun x => w x i) j y) k z) =
          fun _ => 0 := by
      funext z i j k
      simp [w, spatialPartial]
    have htime :
        (fun z i => timePartial (fun y => w y i) z) = fun _ => 0 := by
      funext z i
      simp [w, timePartial]
    simpa only [w, hfirst, hsecond, htime] using hweak

end ESS

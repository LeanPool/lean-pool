/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocity

/-!
# Classical spatial regularity of the regularized velocity

When the global regularized mild curve lifts continuously to the Bessel
potential space of order four on every interval `[0,T]`, the pointwise
velocity of `thm:regularised`, its first and its second spatial partial
derivatives are continuous on `ℝ³ × (0,∞)`, and the velocity slices and their
first partial derivatives are differentiable.
-/

public section

open MeasureTheory FourierTransform Complex Set
open scoped ENNReal FourierTransform Real

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- A spatial partial derivative depends only on the time slice. -/
theorem regR12_spatialPartial_congr_slice {F F' : ParabolicPoint → ℝ} (z : ParabolicPoint)
    (h : ∀ x : Vec3, F (x, z.2) = F' (x, z.2)) (j : Fin 3) :
    spatialPartial F j z = spatialPartial F' j z := by
  unfold spatialPartial
  have hfun : (fun x : Vec3 => F (x, z.2)) = fun x => F' (x, z.2) := funext h
  rw [hfun]

/-- A field that agrees on every slab `ℝ³ × (0,T)` with a continuous field is
continuous on `ℝ³ × (0,∞)` for the parabolic topology. -/
theorem regR12_continuousOn_of_local_models {F : ParabolicPoint → ℝ}
    (h : ∀ T : ℝ, 0 < T → ∃ F' : Vec3 × ℝ → ℝ, Continuous F' ∧
      ∀ z : Vec3 × ℝ, z.2 ∈ Ioo 0 T → F ((z.1, z.2) : ParabolicPoint) = F' z) :
    ContinuousOn F (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) := by
  refine regR12_continuousOn_of_prod (S := Set.univ ×ˢ Ioi 0) ?_
  intro z hz
  have hz0 : 0 < z.2 := hz.2
  obtain ⟨F', hF', hagree⟩ := h (z.2 + 1) (by linarith only [hz0])
  have hnhds : Set.univ ×ˢ Ioo 0 (z.2 + 1) ∈ nhds z :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨Set.mem_univ _, hz0, by linarith only⟩
  have hev : (fun w : Vec3 × ℝ => F ((w.1, w.2) : ParabolicPoint)) =ᶠ[nhds z] F' :=
    Filter.eventually_of_mem hnhds fun w hw => hagree w hw.2
  exact (hF'.continuousAt.congr hev.symm).continuousWithinAt

theorem regR12_one_norm_le (ξ : L2Vec3) : ‖(fun _ : L2Vec3 => (1 : ℂ)) ξ‖ ≤ 1 * (1 + ‖ξ‖ ^ 2) := by
  rw [norm_one, one_mul]
  nlinarith only [sq_nonneg ‖ξ‖]

theorem regR12_one_norm_le' (ξ : L2Vec3) :
    ‖ξ‖ * ‖(fun _ : L2Vec3 => (1 : ℂ)) ξ‖ ≤ 1 * (1 + ‖ξ‖ ^ 2) := by
  rw [norm_one, mul_one, one_mul]
  nlinarith only [sq_nonneg (‖ξ‖ - 1), norm_nonneg ξ]

theorem regR12_first_norm_le (j : Fin 3) (ξ : L2Vec3) :
    ‖(fun ξ => regR12CoordSymbol j ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ) ξ‖ ≤
      (2 * π) * (1 + ‖ξ‖ ^ 2) := by
  simp only [mul_one]
  refine (regR12CoordSymbol_norm_le j ξ).trans ?_
  have h := regR12_one_norm_le' ξ
  rw [norm_one, mul_one, one_mul] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem regR12_first_norm_le' (j : Fin 3) (ξ : L2Vec3) :
    ‖ξ‖ * ‖(fun ξ => regR12CoordSymbol j ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ) ξ‖ ≤
      (2 * π) * (1 + ‖ξ‖ ^ 2) := by
  simp only [mul_one]
  calc ‖ξ‖ * ‖regR12CoordSymbol j ξ‖ ≤ ‖ξ‖ * (2 * π * ‖ξ‖) :=
        mul_le_mul_of_nonneg_left (regR12CoordSymbol_norm_le j ξ) (norm_nonneg ξ)
    _ = (2 * π) * ‖ξ‖ ^ 2 := by ring
    _ ≤ (2 * π) * (1 + ‖ξ‖ ^ 2) := by gcongr; linarith only

theorem regR12_second_norm_le (j k : Fin 3) (ξ : L2Vec3) :
    ‖(fun ξ => regR12CoordSymbol k ξ *
      (fun ξ => regR12CoordSymbol j ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ) ξ) ξ‖ ≤
      (2 * π) ^ 2 * (1 + ‖ξ‖ ^ 2) := by
  simp only [mul_one, norm_mul]
  calc ‖regR12CoordSymbol k ξ‖ * ‖regR12CoordSymbol j ξ‖
      ≤ (2 * π * ‖ξ‖) * (2 * π * ‖ξ‖) :=
        mul_le_mul (regR12CoordSymbol_norm_le k ξ) (regR12CoordSymbol_norm_le j ξ)
          (norm_nonneg _) (by positivity)
    _ = (2 * π) ^ 2 * ‖ξ‖ ^ 2 := by ring
    _ ≤ (2 * π) ^ 2 * (1 + ‖ξ‖ ^ 2) := by gcongr; linarith only

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (a : Vec3 → Vec3) (ha : CKN.IsInJ a)

section Model

variable (T : ℝ) (hT : 0 ≤ T)
  (v : C(RegularizedMildTimeInterval T,
    BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
  (hv : ∀ t : RegularizedMildTimeInterval T,
    regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) regR12_besselOrder_nonneg (v t) =
      complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))

include hv in
/-- On `[0,T]`, the first spatial partial derivatives of the velocity are the
space-time fields of the lift with the multiplier `2πi ξ_j`. -/
theorem regR12Velocity_D_eq_model (z : ParabolicPoint) (hz : z.2 ∈ Icc 0 T) (i j : Fin 3) :
    spatialPartial (fun y => regR12Velocity ρ ε hε a ha y i) j z =
      regR12SpaceTimeField (regR12CoordCLM i)
        (fun ξ => regR12CoordSymbol j ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ)
        (regR12LiftFreq T hT v) z := by
  rw [regR12_spatialPartial_congr_slice (F' := regR12SpaceTimeField (regR12CoordCLM i)
    (fun _ => 1) (regR12LiftFreq T hT v)) z
    (fun x => regR12Velocity_eq_model ρ ε hε a ha T hT v hv (x, z.2) hz i)]
  exact ((regR12SpaceTimeField_spatialPartial (regR12CoordCLM i) (fun _ => (1 : ℂ))
    aestronglyMeasurable_const 1 zero_le_one regR12_one_norm_le (regR12LiftFreq T hT v)
    regR12_one_norm_le' z).2 j)

include hv in
/-- On `[0,T]`, the second spatial partial derivatives of the velocity are
the space-time fields of the lift with the multiplier `(2πi)² ξ_j ξ_k`. -/
theorem regR12Velocity_DD_eq_model (z : ParabolicPoint) (hz : z.2 ∈ Icc 0 T) (i j k : Fin 3) :
    spatialPartial (fun y => spatialPartial (fun x => regR12Velocity ρ ε hε a ha x i) j y) k z =
      regR12SpaceTimeField (regR12CoordCLM i)
        (fun ξ => regR12CoordSymbol k ξ *
          (fun ξ => regR12CoordSymbol j ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ) ξ)
        (regR12LiftFreq T hT v) z := by
  rw [regR12_spatialPartial_congr_slice (F' := regR12SpaceTimeField (regR12CoordCLM i)
    (fun ξ => regR12CoordSymbol j ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ)
    (regR12LiftFreq T hT v)) z
    (fun x => regR12Velocity_D_eq_model ρ ε hε a ha T hT v hv (x, z.2) hz i j)]
  exact ((regR12SpaceTimeField_spatialPartial (regR12CoordCLM i) _
    (((regR12CoordSymbol_continuous j).mul continuous_const).aestronglyMeasurable)
    (2 * π) (by positivity) (regR12_first_norm_le j) (regR12LiftFreq T hT v)
    (regR12_first_norm_le' j) z).2 k)

include hv hT in
/-- On `[0,T]`, the velocity slices and their first partial derivatives are
differentiable. -/
theorem regR12Velocity_slices_differentiableAt (z : ParabolicPoint) (hz : z.2 ∈ Icc 0 T)
    (i j : Fin 3) :
    DifferentiableAt ℝ (fun x : Vec3 => regR12Velocity ρ ε hε a ha (x, z.2) i) z.1 ∧
      DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => regR12Velocity ρ ε hε a ha y i) j (x, z.2))
        z.1 := by
  constructor
  · have h := (regR12SpaceTimeField_spatialPartial (regR12CoordCLM i) (fun _ => (1 : ℂ))
      aestronglyMeasurable_const 1 zero_le_one regR12_one_norm_le (regR12LiftFreq T hT v)
      regR12_one_norm_le' z).1
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    exact regR12Velocity_eq_model ρ ε hε a ha T hT v hv (x, z.2) hz i
  · have h := (regR12SpaceTimeField_spatialPartial (regR12CoordCLM i) _
      (((regR12CoordSymbol_continuous j).mul continuous_const).aestronglyMeasurable)
      (2 * π) (by positivity) (regR12_first_norm_le j) (regR12LiftFreq T hT v)
      (regR12_first_norm_le' j) z).1
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    exact regR12Velocity_D_eq_model ρ ε hε a ha T hT v hv (x, z.2) hz i j

end Model

section Global

variable (hPath : ∀ T : ℝ, 0 ≤ T → ∃ v : C(RegularizedMildTimeInterval T,
    BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2),
  ∀ t : RegularizedMildTimeInterval T,
    regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) regR12_besselOrder_nonneg (v t) =
      complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))

include hPath in
/-- Every nonnegative-time slice of the velocity represents the global curve. -/
theorem regR12Velocity_slice_ae_eq_curve (t : ℝ) (ht : 0 ≤ t) :
    (fun x : Vec3 => regR12Velocity ρ ε hε a ha (x, t)) =ᵐ[volume]
      realVectorL2Representative (regR12Curve ρ ε hε a ha t) := by
  obtain ⟨v, hv⟩ := hPath t ht
  exact regR12Velocity_slice_ae_eq ρ ε hε a ha t ht v hv t ⟨ht, le_rfl⟩

include hPath in
/-- The velocity is continuous on `ℝ³ × (0,∞)`. -/
theorem regR12Velocity_continuousOn (i : Fin 3) :
    ContinuousOn (fun z => regR12Velocity ρ ε hε a ha z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) := by
  refine regR12_continuousOn_of_local_models fun T hT => ?_
  obtain ⟨v, hv⟩ := hPath T hT.le
  refine ⟨_, regR12SpaceTimeField_continuous (regR12CoordCLM i) (fun _ => (1 : ℂ))
    aestronglyMeasurable_const 1 zero_le_one regR12_one_norm_le (regR12LiftFreq T hT.le v)
    (regR12LiftFreq_continuous T hT.le v), fun z hz => ?_⟩
  exact regR12Velocity_eq_model ρ ε hε a ha T hT.le v hv (z.1, z.2) ⟨hz.1.le, hz.2.le⟩ i

include hPath in
/-- The first spatial partial derivatives of the velocity are continuous on
`ℝ³ × (0,∞)`. -/
theorem regR12Velocity_D_continuousOn (i j : Fin 3) :
    ContinuousOn (fun z => spatialPartial (fun y => regR12Velocity ρ ε hε a ha y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) := by
  refine regR12_continuousOn_of_local_models fun T hT => ?_
  obtain ⟨v, hv⟩ := hPath T hT.le
  refine ⟨_, regR12SpaceTimeField_continuous (regR12CoordCLM i) _
    (((regR12CoordSymbol_continuous j).mul continuous_const).aestronglyMeasurable)
    (2 * π) (by positivity) (regR12_first_norm_le j) (regR12LiftFreq T hT.le v)
    (regR12LiftFreq_continuous T hT.le v), fun z hz => ?_⟩
  exact regR12Velocity_D_eq_model ρ ε hε a ha T hT.le v hv (z.1, z.2) ⟨hz.1.le, hz.2.le⟩ i j

include hPath in
/-- The second spatial partial derivatives of the velocity are continuous on
`ℝ³ × (0,∞)`. -/
theorem regR12Velocity_DD_continuousOn (i j k : Fin 3) :
    ContinuousOn (fun z => spatialPartial
      (fun y => spatialPartial (fun x => regR12Velocity ρ ε hε a ha x i) j y) k z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) := by
  refine regR12_continuousOn_of_local_models fun T hT => ?_
  obtain ⟨v, hv⟩ := hPath T hT.le
  refine ⟨_, regR12SpaceTimeField_continuous (regR12CoordCLM i) _
    (((regR12CoordSymbol_continuous k).mul
      ((regR12CoordSymbol_continuous j).mul continuous_const)).aestronglyMeasurable)
    ((2 * π) ^ 2) (by positivity) (regR12_second_norm_le j k) (regR12LiftFreq T hT.le v)
    (regR12LiftFreq_continuous T hT.le v), fun z hz => ?_⟩
  exact regR12Velocity_DD_eq_model ρ ε hε a ha T hT.le v hv (z.1, z.2) ⟨hz.1.le, hz.2.le⟩
    i j k

include hPath in
/-- The velocity slices and their first partial derivatives are differentiable
at positive times. -/
theorem regR12Velocity_differentiableAt (z : ParabolicPoint)
    (hz : z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) (i j : Fin 3) :
    DifferentiableAt ℝ (fun x : Vec3 => regR12Velocity ρ ε hε a ha (x, z.2) i) z.1 ∧
      DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => regR12Velocity ρ ε hε a ha y i) j (x, z.2))
        z.1 := by
  have hz0 : 0 < z.2 := hz.2
  obtain ⟨v, hv⟩ := hPath z.2 hz0.le
  exact regR12Velocity_slices_differentiableAt ρ ε hε a ha z.2 hz0.le v hv z
    ⟨hz0.le, le_rfl⟩ i j

end Global

end CKN.Leray

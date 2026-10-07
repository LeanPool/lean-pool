/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocityReg
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalBounds

/-!
# Strip bounds and slab integrability of the regularized velocity

On every strip `ℝ³ × [δ,T]` the pointwise velocity of `thm:regularised` and
its first and second spatial partial derivatives are bounded, and on every
slab `ℝ³ × (δ,T)` they are square integrable (R2).
-/

public section

open MeasureTheory FourierTransform Complex Set
open scoped ENNReal FourierTransform Real

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (a : Vec3 → Vec3) (ha : CKN.IsInJ a)

/-- A common bound for the coordinate functionals. -/
@[expose]
def regR12CoordBound : ℝ := ∑ i : Fin 3, ‖regR12CoordCLM i‖

theorem regR12CoordCLM_norm_le (i : Fin 3) : ‖regR12CoordCLM i‖ ≤ regR12CoordBound :=
  Finset.single_le_sum (f := fun i => ‖regR12CoordCLM i‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ i)

theorem regR12CoordBound_nonneg : 0 ≤ regR12CoordBound :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

section Model

variable (T : ℝ) (hT : 0 ≤ T)
  (v : C(RegularizedMildTimeInterval T,
    BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
  (hv : ∀ t : RegularizedMildTimeInterval T,
    regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) regR12_besselOrder_nonneg (v t) =
      complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))

/-- The common strip bound of the velocity and its spatial derivatives. -/
@[expose]
def regR12VelocityBound : ℝ :=
  regR12CoordBound * ((2 * π) ^ 2 + 2 * π + 1) *
    (eLpNorm regR12Kernel 2 volume).toReal * ‖v‖

theorem regR12VelocityBound_nonneg : 0 ≤ regR12VelocityBound T v := by
  unfold regR12VelocityBound
  have := regR12CoordBound_nonneg
  positivity

/-- A space-time field of the lift with multiplier constant at most
`(2π)² + 2π + 1` is bounded by the common strip bound. -/
theorem regR12_model_abs_le (i : Fin 3) (M : L2Vec3 → ℂ) (hM : AEStronglyMeasurable M)
    (C : ℝ) (hC : 0 ≤ C) (hCle : C ≤ (2 * π) ^ 2 + 2 * π + 1)
    (hMC : ∀ ξ, ‖M ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2)) (z : ParabolicPoint) :
    |regR12SpaceTimeField (regR12CoordCLM i) M (regR12LiftFreq T hT v) z| ≤
      regR12VelocityBound T v := by
  refine (regR12SpaceTimeField_abs_le (regR12CoordCLM i) M hM C hC hMC
    (regR12LiftFreq T hT v) z).trans ?_
  unfold regR12VelocityBound
  have hK : 0 ≤ (eLpNorm regR12Kernel 2 volume).toReal := ENNReal.toReal_nonneg
  have hG := regR12LiftFreq_norm_le T hT v z.2
  calc ‖regR12CoordCLM i‖ * (C * (eLpNorm regR12Kernel 2 volume).toReal *
        ‖regR12LiftFreq T hT v z.2‖)
      ≤ regR12CoordBound * (((2 * π) ^ 2 + 2 * π + 1) *
          (eLpNorm regR12Kernel 2 volume).toReal * ‖v‖) := by
        gcongr
        · exact regR12CoordBound_nonneg
        · exact regR12CoordCLM_norm_le i
    _ = _ := by ring

end Model

variable (hPath : ∀ T : ℝ, 0 ≤ T → ∃ v : C(RegularizedMildTimeInterval T,
    BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2),
  ∀ t : RegularizedMildTimeInterval T,
    regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) regR12_besselOrder_nonneg (v t) =
      complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))

theorem regR12_mult_const_le_one : (1 : ℝ) ≤ (2 * π) ^ 2 + 2 * π + 1 := by
  have : 0 ≤ 2 * π := by positivity
  nlinarith only [this]

theorem regR12_mult_const_le_first : 2 * π ≤ (2 * π) ^ 2 + 2 * π + 1 := by
  nlinarith only [sq_nonneg (2 * π)]

theorem regR12_mult_const_le_second : (2 * π) ^ 2 ≤ (2 * π) ^ 2 + 2 * π + 1 := by
  have : 0 ≤ 2 * π := by positivity
  linarith only [this]

include hPath in
/-- Strip bounds for the velocity and its first and second spatial partial
derivatives. -/
theorem regR12Velocity_strip_bounds (δ T : ℝ) (hδ : 0 < δ) (hδT : δ < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
      vec3EuclideanNorm (regR12Velocity ρ ε hε a ha z) ≤ C ∧
      (∀ i j : Fin 3, |spatialPartial (fun y => regR12Velocity ρ ε hε a ha y i) j z| ≤ C) ∧
      (∀ i j k : Fin 3, |spatialPartial
        (fun y => spatialPartial (fun x => regR12Velocity ρ ε hε a ha x i) j y) k z| ≤ C) := by
  have hT : 0 ≤ T := by linarith only [hδ, hδT]
  obtain ⟨v, hv⟩ := hPath T hT
  have hB := regR12VelocityBound_nonneg T v
  refine ⟨3 * regR12VelocityBound T v, by positivity, fun z hz => ?_⟩
  have hzT : z.2 ∈ Icc 0 T := ⟨hδ.le.trans hz.2.1, hz.2.2⟩
  have hu : ∀ i, |regR12Velocity ρ ε hε a ha z i| ≤ regR12VelocityBound T v := by
    intro i
    rw [regR12Velocity_eq_model ρ ε hε a ha T hT v hv z hzT i]
    exact regR12_model_abs_le T hT v i _ aestronglyMeasurable_const 1 zero_le_one
      regR12_mult_const_le_one regR12_one_norm_le z
  refine ⟨?_, fun i j => ?_, fun i j k => ?_⟩
  · refine (vec3EuclideanNorm_le_sum_abs _).trans ?_
    calc ∑ i : Fin 3, |regR12Velocity ρ ε hε a ha z i|
        ≤ ∑ _i : Fin 3, regR12VelocityBound T v := Finset.sum_le_sum fun i _ => hu i
      _ = 3 * regR12VelocityBound T v := by simp
  · rw [regR12Velocity_D_eq_model ρ ε hε a ha T hT v hv z hzT i j]
    refine (regR12_model_abs_le T hT v i _
      (((regR12CoordSymbol_continuous j).mul continuous_const).aestronglyMeasurable)
      (2 * π) (by positivity) regR12_mult_const_le_first (regR12_first_norm_le j) z).trans ?_
    linarith only [hB]
  · rw [regR12Velocity_DD_eq_model ρ ε hε a ha T hT v hv z hzT i j k]
    refine (regR12_model_abs_le T hT v i _
      (((regR12CoordSymbol_continuous k).mul
        ((regR12CoordSymbol_continuous j).mul continuous_const)).aestronglyMeasurable)
      ((2 * π) ^ 2) (by positivity) regR12_mult_const_le_second
      (regR12_second_norm_le j k) z).trans ?_
    linarith only [hB]

include hPath in
/-- Square integrability of the velocity and its first and second spatial
partial derivatives on slabs. -/
theorem regR12Velocity_slab_memLp (δ T : ℝ) (hδ : 0 < δ) (hδT : δ < T) :
    (∀ i : Fin 3, MemLp (fun z : ParabolicPoint => regR12Velocity ρ ε hε a ha z i) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
    (∀ i j : Fin 3, MemLp (fun z : ParabolicPoint =>
        spatialPartial (fun y => regR12Velocity ρ ε hε a ha y i) j z) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
    (∀ i j k : Fin 3, MemLp (fun z : ParabolicPoint => spatialPartial
        (fun y => spatialPartial (fun x => regR12Velocity ρ ε hε a ha x i) j y) k z) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) := by
  have hT : 0 ≤ T := by linarith only [hδ, hδT]
  obtain ⟨v, hv⟩ := hPath T hT
  have hslab : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hin : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T), z.2 ∈ Icc 0 T :=
    fun z hz => ⟨hδ.le.trans hz.2.1.le, hz.2.2.le⟩
  have hGB : ∀ t ∈ Ioo δ T, ‖regR12LiftFreq T hT v t‖ ≤ ‖v‖ :=
    fun t _ => regR12LiftFreq_norm_le T hT v t
  refine ⟨fun i => ?_, fun i j => ?_, fun i j k => ?_⟩
  · refine (memLp_congr_ae ?_).2 (regR12SpaceTimeField_memLp_slab (regR12CoordCLM i)
      (fun _ => (1 : ℂ)) aestronglyMeasurable_const 1 zero_le_one regR12_one_norm_le
      (regR12LiftFreq T hT v) (regR12LiftFreq_continuous T hT v) δ T ‖v‖ hGB)
    filter_upwards [ae_restrict_mem hslab] with z hz
    exact regR12Velocity_eq_model ρ ε hε a ha T hT v hv z (hin z hz) i
  · refine (memLp_congr_ae ?_).2 (regR12SpaceTimeField_memLp_slab (regR12CoordCLM i) _
      (((regR12CoordSymbol_continuous j).mul continuous_const).aestronglyMeasurable)
      (2 * π) (by positivity) (regR12_first_norm_le j)
      (regR12LiftFreq T hT v) (regR12LiftFreq_continuous T hT v) δ T ‖v‖ hGB)
    filter_upwards [ae_restrict_mem hslab] with z hz
    exact regR12Velocity_D_eq_model ρ ε hε a ha T hT v hv z (hin z hz) i j
  · refine (memLp_congr_ae ?_).2 (regR12SpaceTimeField_memLp_slab (regR12CoordCLM i) _
      (((regR12CoordSymbol_continuous k).mul
        ((regR12CoordSymbol_continuous j).mul continuous_const)).aestronglyMeasurable)
      ((2 * π) ^ 2) (by positivity) (regR12_second_norm_le j k)
      (regR12LiftFreq T hT v) (regR12LiftFreq_continuous T hT v) δ T ‖v‖ hGB)
    filter_upwards [ae_restrict_mem hslab] with z hz
    exact regR12Velocity_DD_eq_model ρ ε hε a ha T hT v hv z (hin z hz) i j k

end CKN.Leray

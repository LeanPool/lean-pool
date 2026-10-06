/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalAssemblySupport
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedPressure

/-!
# The slice and regularity properties (R1)–(R2) of `thm:regularised`

For the pointwise regularized velocity and the canonical Riesz pressure of
the global regularized mild curve, the properties (R1)–(R2) of
`thm:regularised` follow from:
- the continuous lift of the curve to the Bessel potential space of order four;
- the regularity of the pressure;
- the classical time derivative of the velocity;
- joint continuous differentiability from continuous partial derivatives.
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- `thm:regularised` (R1)–(R2) for the pointwise regularized velocity and
the canonical pressure. -/
theorem regR12_R1R2 (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (hPath : ∀ T : ℝ, 0 ≤ T → ∃ v : C(RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2),
      ∀ t : RegularizedMildTimeInterval T,
        regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by positivity) (v t) =
          complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))
    (hPress :
      let p : ParabolicPoint → ℝ := forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha)
      ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
      (∀ i : Fin 3, ContinuousOn (fun z => spatialPartial (fun y => p y) i z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
          |p z| ≤ C ∧ ∀ i : Fin 3, |spatialPartial (fun y => p y) i z| ≤ C) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) ∧
        ∀ i : Fin 3, MemLp (fun z => spatialPartial (fun y => p y) i z) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))))
    (hTime : ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      HasDerivAt (fun s : ℝ => regR12Velocity ρ ε hε a ha (z.1, s) i)
        (regR12TimeRHS ρ ε hε (regR12Velocity ρ ε hε a ha)
          (forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha)) z i) z.2)
    (hJoint : ∀ (f g : ParabolicPoint → ℝ),
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        DifferentiableAt ℝ (fun x : Vec3 => f (x, z.2)) z.1) →
      (∀ j : Fin 3, ContinuousOn (fun z => spatialPartial f j z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) →
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        HasDerivAt (fun s : ℝ => f (z.1, s)) (g z) z.2) →
      ContinuousOn g (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) →
      letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ContDiffOn ℝ 1 f (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) :
    let u := regR12Velocity ρ ε hε a ha
    let p : ParabolicPoint → ℝ := forcedQuadPressure ρ ε hε (regR12Curve ρ ε hε a ha)
    let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun y => u y i) j z
    let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
      spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
    let Dt : ParabolicPoint → Vec3 := fun z i =>
      timePartial (fun y => u y i) z
    let Dp : ParabolicPoint → Vec3 := fun z i =>
      spatialPartial (fun y => p y) i z
    (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        CKN.Leray.realVectorL2OfCoordinateFunction
          (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
      (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
        CKN.Leray.regUniformMollifiedInitial ρ ε hε a ∧
      ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
    (∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j, ContinuousOn (fun z => D z i j)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j k, ContinuousOn (fun z => DD z i j k)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i, ContinuousOn (fun z => Dt z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
    (∀ i, ContinuousOn (fun z => Dp z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
     letI : NormedAddCommGroup ParabolicPoint :=
       inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
     letI : NormedSpace ℝ ParabolicPoint :=
       inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
     ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
      DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
          vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
          (∀ i j, |D z i j| ≤ C) ∧
          (∀ i j k, |DD z i j k| ≤ C) ∧
          (∀ i, |Dt z i| ≤ C) ∧
          (∀ i, |Dp z i| ≤ C)) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      MemLp p 2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) := by
  intro u p D DD Dt Dp
  obtain ⟨hPc, hDpc, hPdiff, hPbound, hPL2⟩ := hPress
  have hSlicePos : ∀ t : ℝ, 0 < t → MemLp (fun x : Vec3 => u (x, t)) 2 volume := by
    obtain ⟨hSlice, -⟩ := regR12Velocity_R1 ρ ε hε a ha hPath
    exact fun t ht => hSlice t ht.le
  have hUc := regR12Velocity_continuousOn ρ ε hε a ha hPath
  have hDc := regR12Velocity_D_continuousOn ρ ε hε a ha hPath
  have hDDc := regR12Velocity_DD_continuousOn ρ ε hε a ha hPath
  have hGc : ∀ i : Fin 3, ContinuousOn (fun z => regR12TimeRHS ρ ε hε u p z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) :=
    regR12TimeRHS_continuousOn ρ ε hε u p hSlicePos hUc hDc hDDc hDpc
  have hDtEq : ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      Dt z i = regR12TimeRHS ρ ε hε u p z i :=
    fun z hz i => regR12_timePartial_eq_of_hasDerivAt (hTime z hz i)
  have hDtc : ∀ i : Fin 3, ContinuousOn (fun z => Dt z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) :=
    fun i => (hGc i).congr fun z hz => hDtEq z hz.2 i
  refine ⟨regR12Velocity_R1 ρ ε hε a ha hPath, hUc, hDc, hDDc, hDtc, hPc, hDpc, ?_,
    fun z hz i j => (regR12Velocity_differentiableAt ρ ε hε a ha hPath z hz i j).2, hPdiff,
    ?_, ?_⟩
  · intro i
    exact hJoint (fun z => u z i) (fun z => regR12TimeRHS ρ ε hε u p z i)
      (fun z hz => (regR12Velocity_differentiableAt ρ ε hε a ha hPath z hz i i).1)
      (hDc i) (fun z hz => hTime z hz.2 i) (hGc i)
  · intro δ T hδ hδT
    obtain ⟨Cu, hCu, hUb⟩ := regR12Velocity_strip_bounds ρ ε hε a ha hPath δ T hδ hδT
    obtain ⟨Cp, hCp, hPb⟩ := hPbound δ T hδ hδT
    let C0 : ℝ := Cu + Cp
    set K : ℝ := ∫ y : Vec3, |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)| with hK_def
    have hK : 0 ≤ K := integral_nonneg fun _ => abs_nonneg _
    refine ⟨C0 + (3 * C0 + 3 * ((C0 * K) * C0) + C0), by positivity, fun z hz => ?_⟩
    have hstrip : ∀ x : Vec3, (x, z.2) ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T) :=
      fun x => ⟨Set.mem_univ _, hz.2⟩
    have hz0 : 0 < z.2 := lt_of_lt_of_le hδ hz.2.1
    have hG := regR12TimeRHS_abs_le ρ ε hε u p hSlicePos C0 z.2 hz0
      (fun x => (hUb (x, z.2) (hstrip x)).1.trans (by linarith only [hCp]))
      (fun x i j => ((hUb (x, z.2) (hstrip x)).2.1 i j).trans (by linarith only [hCp]))
      (fun x i j k => ((hUb (x, z.2) (hstrip x)).2.2 i j k).trans (by linarith only [hCp]))
      (fun x i => ((hPb (x, z.2) (hstrip x)).2 i).trans (by linarith only [hCu])) z.1
    have hC0 : 0 ≤ C0 := by positivity
    have hE : 0 ≤ 3 * C0 + 3 * ((C0 * K) * C0) + C0 := by positivity
    obtain ⟨hu, hD, hDD⟩ := hUb z hz
    obtain ⟨hp, hDp⟩ := hPb z hz
    refine ⟨by linarith only [hu, hCp, hE], by linarith only [hp, hCu, hE],
      fun i j => by linarith only [hD i j, hCp, hE],
      fun i j k => by linarith only [hDD i j k, hCp, hE], fun i => ?_,
      fun i => by linarith only [hDp i, hCu, hE]⟩
    rw [hDtEq z hz0 i]
    have hGi : |regR12TimeRHS ρ ε hε u p z i| ≤ 3 * C0 + 3 * ((C0 * K) * C0) + C0 := hG i
    linarith only [hGi, hC0]
  · intro δ T hδ hδT
    obtain ⟨hUL2, hDL2, hDDL2⟩ := regR12Velocity_slab_memLp ρ ε hε a ha hPath δ T hδ hδT
    obtain ⟨hpL2, hDpL2⟩ := hPL2 δ T hδ hδT
    obtain ⟨Cu, hCu, hUb⟩ := regR12Velocity_strip_bounds ρ ε hε a ha hPath δ T hδ hδT
    have hslab : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)) :=
      MeasurableSet.univ.prod measurableSet_Ioo
    refine ⟨hUL2, hDL2, hDDL2, fun i => ?_, hpL2⟩
    have hJ : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T), ∀ j : Fin 3,
        |regUniformMollifiedVelocity ρ ε hε u z j| ≤
          Cu * ∫ y : Vec3, |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)| := by
      intro z hz j
      have hz0 : 0 < z.2 := lt_trans hδ hz.2.1
      exact regR12_mollifiedVelocity_abs_le ρ ε hε u z.2 (hSlicePos z.2 hz0) Cu
        (fun x i' => (abs_apply_le_vec3EuclideanNorm _ i').trans
          (hUb (x, z.2) ⟨Set.mem_univ _, hz.2.1.le, hz.2.2.le⟩).1) z.1 j
    have hGL2 := regR12TimeRHS_memLp_slab ρ ε hε u p δ T hSlicePos hUc hDc hδ hDL2 hDDL2 hDpL2
      _ hJ i
    refine (memLp_congr_ae ?_).2 hGL2
    filter_upwards [ae_restrict_mem hslab] with z hz
    exact hDtEq z (lt_trans hδ hz.2.1) i

end CKN.Leray

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.TenThirdsConsumers
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSpaceTimeLp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# The pressure candidate for a Leray–Hopf solution

The velocity tensor, extended by zero outside the time interval, defines the
whole-space Riesz pressure used in `thm:assoc-pressure`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The zero extension of the velocity tensor on the finite time slab,
used by `thm:assoc-pressure`. -/
@[expose]
def associatedPressureTensor (T : ℝ) (u : ParabolicPoint → Vec3) :
    Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j =>
  (parabolicHomeomorph.symm ⁻¹'
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)).indicator
    (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i *
      u (parabolicHomeomorph.symm z) j)

/-- Every component of the zero-extended velocity tensor belongs to
space-time `L^(5/3)`, by `lem:u-ten-thirds`. -/
theorem associatedPressureTensor_memLp_fiveThirds
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) (i j : Fin 3) :
    MemLp (associatedPressureTensor T u i j)
      (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
  rw [associatedPressureTensor, memLp_indicator_iff_restrict
    (parabolicHomeomorph.symm.measurable
      (by exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo))]
  rw [Measure.volume_eq_prod Vec3 ℝ]
  let Q : Set ParabolicPoint :=
    spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have hMap : MeasurePreserving parabolicHomeomorph.symm
      (volume.restrict (parabolicHomeomorph.symm ⁻¹' Q))
      (volume.restrict Q) :=
    parabolicHomeomorphSymm_measurePreserving.restrict_preimage
      (by exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo)
  have hMapProd : MeasurePreserving parabolicHomeomorph.symm
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (parabolicHomeomorph.symm ⁻¹' Q))
      (volume.restrict Q) := by
    rw [← Measure.volume_eq_prod Vec3 ℝ]
    exact hMap
  have hcomp :=
    (lerayHopf_tensor_memLp_fiveThirds hLH i j).comp_measurePreserving hMapProd
  change MemLp
    (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i *
      u (parabolicHomeomorph.symm z) j)
    (ENNReal.ofReal (5 / 3 : ℝ))
    (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      (parabolicHomeomorph.symm ⁻¹' spaceTimeSet
        (Set.univ : Set Vec3) (Ioo 0 T))) at hcomp
  exact hcomp

/-- Every component of the zero-extended velocity tensor belongs to
space-time `L^(3/2)`, by the finite-time `L^3` energy interpolation. -/
theorem associatedPressureTensor_memLp_threeHalves
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) (i j : Fin 3) :
    MemLp (associatedPressureTensor T u i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
  classical
  let : ENNReal.HolderTriple (ENNReal.ofReal (3 : ℝ))
      (ENNReal.ofReal (3 : ℝ)) (ENNReal.ofReal (3 / 2 : ℝ)) := by
    have h : Real.HolderTriple (3 : ℝ) 3 (3 / 2 : ℝ) :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    exact h.ennrealOfReal
  have hU : MemLp u (ENNReal.ofReal (3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    (lerayHopf_memLp_three_with_energy_bound hLH).1
  have hi : MemLp (fun z : ParabolicPoint => u z i)
      (ENNReal.ofReal (3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    (memLp_pi_iff.mp hU) i
  have hj : MemLp (fun z : ParabolicPoint => u z j)
      (ENNReal.ofReal (3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    (memLp_pi_iff.mp hU) j
  have hproduct : MemLp (fun z : ParabolicPoint => u z i * u z j)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    have hfun : (fun z : ParabolicPoint => u z i * u z j) =
        (fun z => u z i) * (fun z => u z j) := rfl
    rw [hfun]
    exact hi.mul hj
  rw [associatedPressureTensor, memLp_indicator_iff_restrict
    (parabolicHomeomorph.symm.measurable
      (by exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo))]
  rw [Measure.volume_eq_prod Vec3 ℝ]
  let Q : Set ParabolicPoint :=
    spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have hMap : MeasurePreserving parabolicHomeomorph.symm
      (volume.restrict (parabolicHomeomorph.symm ⁻¹' Q))
      (volume.restrict Q) :=
    parabolicHomeomorphSymm_measurePreserving.restrict_preimage
      (by exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo)
  have hMapProd : MeasurePreserving parabolicHomeomorph.symm
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (parabolicHomeomorph.symm ⁻¹' Q))
      (volume.restrict Q) := by
    rw [← Measure.volume_eq_prod Vec3 ℝ]
    exact hMap
  have hcomp := hproduct.comp_measurePreserving hMapProd
  change MemLp
    (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i *
      u (parabolicHomeomorph.symm z) j)
    (ENNReal.ofReal (3 / 2 : ℝ))
    (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      (parabolicHomeomorph.symm ⁻¹' spaceTimeSet
        (Set.univ : Set Vec3) (Ioo 0 T))) at hcomp
  exact hcomp

/-- The jointly measurable Riesz pressure selected for `thm:assoc-pressure`. -/
@[expose]
noncomputable def associatedPressureCandidate
    (T : ℝ) (u : ParabolicPoint → Vec3)
    (hF : ∀ i j, MemLp (associatedPressureTensor T u i j)
      (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ))) :
    ParabolicPoint → ℝ :=
  (rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
    (associatedPressureTensor T u) hF) ∘ parabolicHomeomorph

/-- The associated pressure candidate belongs to space-time `L^(5/3)`, as in
`thm:assoc-pressure`. -/
theorem associatedPressureCandidate_memLp_fiveThirds
    (T : ℝ) (u : ParabolicPoint → Vec3)
    (hF : ∀ i j, MemLp (associatedPressureTensor T u i j)
      (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ))) :
    MemLp (associatedPressureCandidate T u hF)
      (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure ParabolicPoint) := by
  exact (rieszPressureSpaceTime_memLp (5 / 3 : ℝ) (by norm_num)
    (associatedPressureTensor T u) hF).comp_measurePreserving
      parabolicHomeomorph_measurePreserving

/-- The pressure candidate has the global `L^(5/3)` membership required by
`thm:assoc-pressure` on the finite time slab. -/
theorem associatedPressureCandidate_memLp_on_slab
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    MemLp
      (associatedPressureCandidate T u (associatedPressureTensor_memLp_fiveThirds hLH))
      (ENNReal.ofReal (5 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  exact (associatedPressureCandidate_memLp_fiveThirds T u
    (associatedPressureTensor_memLp_fiveThirds hLH)).restrict _

/-- The pressure selected from a Leray–Hopf solution's velocity tensor. -/
@[expose]
noncomputable def associatedPressureForSolution
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) : ParabolicPoint → ℝ :=
  associatedPressureCandidate T u (associatedPressureTensor_memLp_fiveThirds hLH)

/-- The pressure selected for `thm:assoc-pressure` has the required
space-time `L^(5/3)` membership. -/
theorem associatedPressureForSolution_memLp_fiveThirds
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    MemLp (associatedPressureForSolution hLH)
      (ENNReal.ofReal (5 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
  associatedPressureCandidate_memLp_on_slab hLH

end CKN.Leray

end

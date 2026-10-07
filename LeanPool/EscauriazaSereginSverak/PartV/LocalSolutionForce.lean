/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRough
public import LeanPool.EscauriazaSereginSverak.PartV.StokesPressure
public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbit
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageAgreement

/-!
# The Navier–Stokes forcing of the short-time construction

For a velocity `U` on the slab `ℝ³ × (0, σ)` the construction of
`prop:pv-local-solution` uses the quadratic tensor `U ⊗ U` and its canonical
Riesz pressure, both cut off to the slab, and the forcing tensor
`-(U ⊗ U + p I)`. The Duhamel map adds the forced heat response of this tensor
to the heat orbit of the datum. This file sets up these objects and their
integrability.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The quadratic tensor `U ⊗ V`, cut off to the slab `ℝ³ × (0, σ)`. -/
@[expose] def pvSlabTensor (σ : ℝ) (U V : ParabolicPoint → Vec3) :
    Fin 3 → Fin 3 → ParabolicPoint → ℝ :=
  fun i j => (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)).indicator
    (fun z => U z i * V z j)

open scoped Classical in
/-- The canonical pressure of `U ⊗ U` (the double Riesz transform at exponent
two), cut off to the slab. -/
@[expose] def pvSlabPressure (σ : ℝ) (U : ParabolicPoint → Vec3) : ParabolicPoint → ℝ :=
  (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)).indicator fun z =>
    if h : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal 2)
        (volume : Measure (Vec3 × ℝ)) then
      CKN.Leray.rieszPressureSpaceTime 2 (by norm_num) (pvSlabTensor σ U U) h z
    else 0

/-- The Navier–Stokes forcing tensor `-(U ⊗ U + p I)` on the slab. -/
@[expose] def pvSlabForce (σ : ℝ) (U : ParabolicPoint → Vec3) :
    Fin 3 → Fin 3 → ParabolicPoint → ℝ :=
  fun i j z => -(pvSlabTensor σ U U i j z + if i = j then pvSlabPressure σ U z else 0)

/-- The Duhamel map of `prop:pv-local-solution`: heat orbit of the datum plus
the forced heat response of the Navier–Stokes forcing. -/
@[expose] def pvLocalMap (a : Vec3 → Vec3) (σ : ℝ) (U : ParabolicPoint → Vec3) :
    ParabolicPoint → Vec3 :=
  fun z => heatOrbit a z + forcedHeat (pvSlabForce σ U) z

theorem pvSlab_measurableSet (σ : ℝ) :
    MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)) :=
  MeasurableSet.univ.prod measurableSet_Ioo

theorem pvSlabTensor_eq_zero {σ : ℝ} {U V : ParabolicPoint → Vec3} {z : ParabolicPoint}
    (hz : z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)) (i j : Fin 3) :
    pvSlabTensor σ U V i j z = 0 :=
  indicator_of_notMem hz _

theorem pvSlabPressure_eq_zero {σ : ℝ} {U : ParabolicPoint → Vec3} {z : ParabolicPoint}
    (hz : z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)) :
    pvSlabPressure σ U z = 0 :=
  indicator_of_notMem hz _

theorem pvSlabForce_eq_zero {σ : ℝ} {U : ParabolicPoint → Vec3} {z : ParabolicPoint}
    (hz : z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)) (i j : Fin 3) :
    pvSlabForce σ U i j z = 0 := by
  simp [pvSlabForce, pvSlabTensor_eq_zero hz, pvSlabPressure_eq_zero hz]

/-- On the slab, the pressure is the canonical Riesz pressure of `U ⊗ U`. -/
theorem pvSlabPressure_eq {σ : ℝ} {U : ParabolicPoint → Vec3}
    (hT : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal 2)
      (volume : Measure (Vec3 × ℝ))) :
    pvSlabPressure σ U = (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)).indicator
      (CKN.Leray.rieszPressureSpaceTime 2 (by norm_num) (pvSlabTensor σ U U) hT) := by
  unfold pvSlabPressure
  congr 1
  funext z
  split_ifs with h
  · rfl
  · exact absurd hT h

/-- Hölder's inequality for one entry of the cut-off quadratic tensor. -/
theorem pvSlabTensor_eLpNorm_le {σ : ℝ} {U V : ParabolicPoint → Vec3} {p r : ℝ≥0∞}
    [ENNReal.HolderTriple p p r]
    (hU : AEStronglyMeasurable U
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))))
    (hV : AEStronglyMeasurable V
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))))
    (i j : Fin 3) :
    eLpNorm (pvSlabTensor σ U V i j) r volume ≤
      eLpNorm U p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) *
        eLpNorm V p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) := by
  unfold pvSlabTensor
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (pvSlab_measurableSet σ)]
  have hb : Continuous (Function.uncurry fun (u v : Vec3) => u i * v j) :=
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := p) (q := p) (r := r)
    (fun (u v : Vec3) => u i * v j) 1 hb hU hV (Eventually.of_forall fun z => by
      rw [norm_mul, NNReal.coe_one, one_mul]
      exact mul_le_mul (norm_le_pi_norm _ i) (norm_le_pi_norm _ j) (norm_nonneg _)
        (norm_nonneg _))
  simpa using h

/-- Each entry of the cut-off quadratic tensor lies in `L^r` for velocities in
`L^p` of the slab, `2/p = 1/r`. -/
theorem pvSlabTensor_memLp {σ : ℝ} {U V : ParabolicPoint → Vec3} {p r : ℝ≥0∞}
    [ENNReal.HolderTriple p p r]
    (hU : MemLp U p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))))
    (hV : MemLp V p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))))
    (i j : Fin 3) :
    MemLp (pvSlabTensor σ U V i j) r volume := by
  rw [memLp_iff]
  exact (pvSlabTensor_eLpNorm_le hU.aestronglyMeasurable hV.aestronglyMeasurable i j).trans_lt
    (ENNReal.mul_lt_top hU.eLpNorm_lt_top hV.eLpNorm_lt_top)

/-- The difference of two quadratic tensors splits into two bilinear terms. -/
theorem pvSlabTensor_sub (σ : ℝ) (U V : ParabolicPoint → Vec3) (i j : Fin 3) :
    pvSlabTensor σ U U i j - pvSlabTensor σ V V i j =
      pvSlabTensor σ (U - V) U i j + pvSlabTensor σ V (U - V) i j := by
  funext z
  by_cases hz : z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)
  · simp only [pvSlabTensor, Pi.sub_apply, Pi.add_apply, indicator_of_mem hz]
    ring
  · simp [pvSlabTensor_eq_zero hz]

theorem pvSlab_holderTriple_five : ENNReal.HolderTriple (ENNReal.ofReal 5) (ENNReal.ofReal 5)
    (ENNReal.ofReal (5 / 2)) := by
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 5),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 5 / 2),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

theorem pvSlab_holderTriple_four : ENNReal.HolderTriple (ENNReal.ofReal 4) (ENNReal.ofReal 4)
    (ENNReal.ofReal 2) := by
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

end ESS

end

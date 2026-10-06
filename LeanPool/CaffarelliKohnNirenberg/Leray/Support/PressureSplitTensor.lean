/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyCylinderL4
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.HolderTripleProducts
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# Pressure Split Tensor

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

@[expose]
def pressureSplitSourceDomain : Set ParabolicPoint :=
  spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0)

/-- The tensor used by the pressure split, extended by zero outside the unit
space-time cylinder. -/
@[expose]
def pressureSplitTensor (u : ParabolicPoint → Vec3) (i j : Fin 3) :
    Vec3 × ℝ → ℝ :=
  fun z => pressureSplitSourceDomain.indicator
    (fun q : ParabolicPoint => u q i * u q j) (parabolicHomeomorph.symm z)

private theorem pressureSplitSourceDomain_isFiniteMeasure :
    IsFiniteMeasure ((volume : Measure ParabolicPoint).restrict
      pressureSplitSourceDomain) := by
  let B : Set Vec3 := vec3Ball (0 : Vec3) 1
  let J : Set ℝ := Ioo (-1 : ℝ) 0
  have hsub : pressureSplitSourceDomain ⊆ parabolicCylinder 0 1 2 := by
    intro z hz
    have hx : z.1 ∈ vec3Ball (0 : Vec3) 2 := by
      have hx' : vec3EuclideanNorm z.1 < 1 := by
        simpa [vec3Ball] using hz.1
      change vec3EuclideanNorm (z.1 - 0) < 2
      simpa using lt_trans hx' (by norm_num : (1 : ℝ) < 2)
    have ht : z.2 ∈ Ioc (1 - (2 : ℝ)^2) 1 := by
      have htime : z.2 ∈ Ioo (-1 : ℝ) 0 := hz.2
      constructor
      · norm_num
        linarith only [htime.1]
      · linarith only [htime.2]
    change z.1 ∈ vec3Ball (0 : Vec3) 2 ∧ z.2 ∈ Ioc (1 - (2 : ℝ)^2) 1
    exact ⟨hx, ht⟩
  have hmeasure : volume pressureSplitSourceDomain < ⊤ := by
    exact lt_of_le_of_lt (measure_mono hsub)
      (CKN.Foundation.Parabolic.Integration.volume_parabolicCylinder_lt_top
        (x := (0 : Vec3)) (t := 1) (r := 2))
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact hmeasure

/-- The zero-extended tensor has space-time `L^(3/2)` under the local
energy, `L^infinity_t L^3_x`, and weak-gradient hypotheses. -/
theorem pressureSplitTensor_memLp
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ k : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) k) (fun x => Du (x, t) k)) :
    ∀ i j : Fin 3,
      MemLp (pressureSplitTensor u i j) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume : Measure (Vec3 × ℝ)) := by
  have hu4 : MemLp u 4
      (volume.restrict pressureSplitSourceDomain) := by
    simpa [pressureSplitSourceDomain] using
      velocity_memLp_four_unit_of_essLocalData hu hDu henergy hL3 hgrad
  let : IsFiniteMeasure (volume.restrict pressureSplitSourceDomain) :=
    pressureSplitSourceDomain_isFiniteMeasure
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
    have h : (3 : ℝ).HolderTriple 3 (3 / 2 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    simpa only [hcoeff,
      show ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) by norm_num] using h.ennrealOfReal
  intro i j
  have hui4 : MemLp (fun z : ParabolicPoint => u z i) 4
      (volume.restrict pressureSplitSourceDomain) := (memLp_pi_iff.mp hu4) i
  have huj4 : MemLp (fun z : ParabolicPoint => u z j) 4
      (volume.restrict pressureSplitSourceDomain) := (memLp_pi_iff.mp hu4) j
  have hui3 : MemLp (fun z : ParabolicPoint => u z i) 3
      (volume.restrict pressureSplitSourceDomain) := by
    exact hui4.mono_exponent (by norm_num)
  have huj3 : MemLp (fun z : ParabolicPoint => u z j) 3
      (volume.restrict pressureSplitSourceDomain) := by
    exact huj4.mono_exponent (by norm_num)
  have hprod : MemLp (fun z : ParabolicPoint => u z i * u z j)
      (3 / 2 : ℝ≥0∞) (volume.restrict pressureSplitSourceDomain) :=
    hui3.mul huj3
  have hdomain : MeasurableSet pressureSplitSourceDomain := by
    exact (isOpen_spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0)
      (isOpen_vec3Ball (0 : Vec3) 1) isOpen_Ioo).measurableSet
  have hglobal : MemLp
      (pressureSplitSourceDomain.indicator (fun z : ParabolicPoint => u z i * u z j))
      (3 / 2 : ℝ≥0∞) (volume : Measure ParabolicPoint) :=
    (memLp_indicator_iff_restrict hdomain).2 hprod
  have hglobalProd := hglobal.comp_measurePreserving
    parabolicHomeomorphSymm_measurePreserving
  rw [hcoeff]
  change MemLp ((pressureSplitSourceDomain.indicator
      (fun z : ParabolicPoint => u z i * u z j)) ∘ parabolicHomeomorph.symm)
    (3 / 2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))
  exact hglobalProd

end CKN

end

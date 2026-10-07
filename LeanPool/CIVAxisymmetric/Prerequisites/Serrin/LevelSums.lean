/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.Vorticity
public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation

/-!
# Level sums for the interior estimates

The sums of absolute values of the vorticity, of its first and second spatial derivatives, and
of the first and second spatial derivatives of the velocity, which carry the successive levels
of the interior estimates in the proof of `lem:aniso:annulus`, with their nonnegativity and
their continuity on the unit cylinder for a smooth velocity.
-/

public section

open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- `∑ᵢ |ωᵢ|`. -/
@[expose] def vortSum0 (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  ∑ i, |curlComp u i z|

/-- `∑ᵢⱼ |∂ⱼωᵢ|`. -/
@[expose] def vortSum1 (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  ∑ i, ∑ j, |spatialPartial (curlComp u i) j z|

/-- `∑ᵢⱼₗ |∂ₗ∂ⱼωᵢ|`. -/
@[expose] def vortSum2 (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  ∑ i, ∑ j, ∑ l, |spatialPartial (fun w => spatialPartial (curlComp u i) j w) l z|

/-- `∑ᵢⱼ |∂ⱼuᵢ|`. -/
@[expose] def velSum1 (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  ∑ i, ∑ j, |spatialPartial (fun w => u w i) j z|

/-- `∑ᵢⱼₗ |∂ₗ∂ⱼuᵢ|`. -/
@[expose] def velSum2 (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  ∑ i, ∑ j, ∑ l, |spatialPartial (fun w => spatialPartial (fun w' => u w' i) j w) l z|

/-- The five level sums are nonnegative. -/
theorem levelSums_nonneg (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    0 ≤ vortSum0 u z ∧ 0 ≤ vortSum1 u z ∧ 0 ≤ vortSum2 u z ∧ 0 ≤ velSum1 u z ∧
      0 ≤ velSum2 u z := by
  refine ⟨Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_, ?_, ?_, ?_⟩ <;>
  · refine Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => ?_))
    first
    | exact abs_nonneg _
    | exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- The vorticity components of a velocity smooth on the unit cylinder are smooth there. -/
theorem contDiffOn_curlComp_unitCylinder {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => curlComp u i z) unitCylinder :=
  (contDiffOn_spatialPartial ((contDiffOn_pi.mp hu) (i + 2)) (i + 1)).sub
    (contDiffOn_spatialPartial ((contDiffOn_pi.mp hu) (i + 1)) (i + 2))

/-- For a velocity smooth on the unit cylinder the five level sums are continuous there. -/
theorem continuousOn_levelSums {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContinuousOn (fun z : Vec3 × ℝ => vortSum0 u z) unitCylinder ∧
      ContinuousOn (fun z : Vec3 × ℝ => vortSum1 u z) unitCylinder ∧
      ContinuousOn (fun z : Vec3 × ℝ => vortSum2 u z) unitCylinder ∧
      ContinuousOn (fun z : Vec3 × ℝ => velSum1 u z) unitCylinder ∧
      ContinuousOn (fun z : Vec3 × ℝ => velSum2 u z) unitCylinder := by
  have hc := contDiffOn_curlComp_unitCylinder hu
  have hcomp : ∀ j : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z j) unitCylinder :=
    fun j => (contDiffOn_pi.mp hu) j
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact continuousOn_finsetSum _ (fun i _ => (hc i).continuousOn.abs)
  · exact continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ =>
      (contDiffOn_spatialPartial (hc i) j).continuousOn.abs))
  · exact continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ =>
      continuousOn_finsetSum _ (fun l _ =>
        (contDiffOn_spatialPartial (contDiffOn_spatialPartial (hc i) j) l).continuousOn.abs)))
  · exact continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ =>
      (contDiffOn_spatialPartial (hcomp i) j).continuousOn.abs))
  · exact continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ =>
      continuousOn_finsetSum _ (fun l _ =>
        (contDiffOn_spatialPartial (contDiffOn_spatialPartial (hcomp i) j) l).continuousOn.abs)))

end CIV

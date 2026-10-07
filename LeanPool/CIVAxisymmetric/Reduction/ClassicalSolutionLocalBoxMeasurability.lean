/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
A classical `ContDiffOn ℝ ⊤` solution on an open space-time box is
`AEStronglyMeasurable` with respect to the restricted volume measure.
These are the four per-local-box measurability conjuncts of
`CKN.IsSuitableWeakSolution` for a smooth solution, obtained directly
from smoothness rather than from weak-solution hypotheses.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section



namespace CIV

/-- A function `v : ParabolicPoint → β` that is `ContDiffOn ℝ ⊤` on a space-time set
`spaceTimeSet Ω' J` (with `Ω'` and `J` open) is `AEStronglyMeasurable` with respect to the
restricted volume measure on that set.  This is the measurability half of the
per-local-box conjunct of `CKN.IsSuitableWeakSolution` for a classical
`ContDiffOn` solution. -/
theorem aestronglyMeasurable_of_contDiffOn_spaceTimeSet {β : Type*} [NormedAddCommGroup β]
    [NormedSpace ℝ β] {v : ParabolicPoint → β} {Ω' : Set Vec3} {J : Set ℝ}
    (hΩ' : IsOpen Ω') (hJ : IsOpen J)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => v z) (spaceTimeSet Ω' J)) :
    AEStronglyMeasurable v (volume.restrict (spaceTimeSet Ω' J)) := by
  have hmeas : MeasurableSet (spaceTimeSet Ω' J) :=
    (hΩ'.prod hJ).measurableSet
  exact hv.continuousOn.aestronglyMeasurable hmeas

/-- The velocity field `u` of a classical `ContDiffOn` solution is
`AEStronglyMeasurable` on any open space-time box. -/
theorem aestronglyMeasurable_u_of_contDiffOn {u : ParabolicPoint → Vec3} {Ω' : Set Vec3}
    {J : Set ℝ} (hΩ' : IsOpen Ω') (hJ : IsOpen J)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) (spaceTimeSet Ω' J)) :
    AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J)) :=
  aestronglyMeasurable_of_contDiffOn_spaceTimeSet hΩ' hJ hu

/-- The pressure field `p` of a classical `ContDiffOn` solution is
`AEStronglyMeasurable` on any open space-time box. -/
theorem aestronglyMeasurable_p_of_contDiffOn {p : ParabolicPoint → ℝ} {Ω' : Set Vec3}
    {J : Set ℝ} (hΩ' : IsOpen Ω') (hJ : IsOpen J)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) (spaceTimeSet Ω' J)) :
    AEStronglyMeasurable p (volume.restrict (spaceTimeSet Ω' J)) :=
  aestronglyMeasurable_of_contDiffOn_spaceTimeSet hΩ' hJ hp

/-- The forcing term `f` of a classical `ContDiffOn` solution is
`AEStronglyMeasurable` on any open space-time box. -/
theorem aestronglyMeasurable_f_of_contDiffOn {f : ParabolicPoint → Vec3} {Ω' : Set Vec3}
    {J : Set ℝ} (hΩ' : IsOpen Ω') (hJ : IsOpen J)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) (spaceTimeSet Ω' J)) :
    AEStronglyMeasurable f (volume.restrict (spaceTimeSet Ω' J)) :=
  aestronglyMeasurable_of_contDiffOn_spaceTimeSet hΩ' hJ hf

/-- The spatial gradient `Du` of a classical `ContDiffOn` solution is
`AEStronglyMeasurable` on any open space-time box. -/
theorem aestronglyMeasurable_Du_of_contDiffOn {Du : ParabolicPoint → Fin 3 → Vec3}
    {Ω' : Set Vec3} {J : Set ℝ} (hΩ' : IsOpen Ω') (hJ : IsOpen J)
    (hDu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => Du z) (spaceTimeSet Ω' J)) :
    AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J)) :=
  aestronglyMeasurable_of_contDiffOn_spaceTimeSet hΩ' hJ hDu

end CIV

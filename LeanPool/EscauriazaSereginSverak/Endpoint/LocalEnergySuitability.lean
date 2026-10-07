/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyCylinderL4
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Data
public import LeanPool.CaffarelliKohnNirenberg.Statements.LocalBox
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative

/-!
# Local Energy Suitability

Local energy identities and limit passages for the endpoint regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace ESS

private theorem vec3Ball_subset_of_r_lt_one {r : ℝ} (hr : r < 1) :
    vec3Ball (0 : Vec3) r ⊆ vec3Ball (0 : Vec3) 1 := by
  intro x hx
  apply mem_vec3Ball.mpr
  calc
    vec3EuclideanNorm (x - 0) < r := mem_vec3Ball.mp hx
    _ < 1 := hr

/-- The local data clauses of CKN's suitable-solution definition follow on every smaller
cylinder from the corresponding hypotheses of `thm:ess-local`. -/
theorem suitableData_of_essLocalData
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {r : ℝ} (hr1 : r < 1)
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i)) :
    CKN.IsSuitableWeakSolutionData (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) 3 u Du p 0 := by
  let Ω : Set Vec3 := vec3Ball (0 : Vec3) r
  let I : Set ℝ := Ioo (-1) 0
  let A := essSup
    (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
    (volume.restrict (Ioo (-1) 0))
  have hAtop : A < ⊤ := by simpa [A] using hL2
  have hΩopen : IsOpen Ω := by
    exact isOpen_vec3Ball (0 : Vec3) r
  have hIopen : IsOpen I := isOpen_Ioo
  have hIord : OrdConnected I := ordConnected_Ioo
  have hΩB : Ω ⊆ vec3Ball (0 : Vec3) 1 := vec3Ball_subset_of_r_lt_one hr1
  refine ⟨hΩopen, hIopen, hIord, by norm_num, ?_, ?_⟩
  · intro Ω' J _hbox i
    change MemLp (fun z : ParabolicPoint => (0 : Vec3) i)
      (ENNReal.ofReal 3) (volume.restrict (spaceTimeSet Ω' J))
    simp
  · intro Ω' J hbox
    have hΩ'sub : Ω' ⊆ Ω := subset_closure.trans hbox.2.2.1
    have hJsub : J ⊆ I := subset_closure.trans hbox.2.2.2.2.2
    have hΩ'B : Ω' ⊆ vec3Ball (0 : Vec3) 1 := hΩ'sub.trans hΩB
    have hsub : spaceTimeSet Ω' J ⊆ spaceTimeSet (vec3Ball (0 : Vec3) 1) I :=
      Set.prod_mono hΩ'B hJsub
    have hmeasure : volume.restrict (spaceTimeSet Ω' J) ≤
        volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) I) :=
      Measure.restrict_mono hsub le_rfl
    have henergy' : (∫⁻ z in spaceTimeSet Ω' J,
        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      refine lt_of_le_of_lt ?_ henergy
      exact lintegral_mono_set hsub
    have hL2ae : ∀ᵐ t ∂(volume.restrict J),
        ∫⁻ x in Ω', ‖u (x, t)‖ₑ ^ (2 : ℝ) ≤ A := by
      have hglobal := ENNReal.ae_le_essSup (μ := volume.restrict I)
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      have hglobalJ := hglobal.filter_mono
        (ae_mono (Measure.restrict_mono hJsub le_rfl))
      filter_upwards [hglobalJ] with t ht
      exact (lintegral_mono_set hΩ'B).trans ht
    have hL2' : essSup (fun t : ℝ => ∫⁻ x in Ω', ‖u (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict J) < ⊤ := by
      refine lt_of_le_of_lt (essSup_le_of_ae_le A hL2ae) hAtop
    have hgrad' : ∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict J),
        HasWeakGradientOn Ω' (fun x => u (x, t) i) (fun x => Du (x, t) i) := by
      have hgradJ := hgrad.filter_mono
        (ae_mono (Measure.restrict_mono hJsub le_rfl))
      intro i
      filter_upwards [hgradJ] with t ht
      exact (ht i).restrict hbox.1 hΩ'B
    exact ⟨hu.mono_measure hmeasure, hDu.mono_measure hmeasure,
      hp.mono_measure hmeasure, aestronglyMeasurable_const,
      hL2', henergy', hpLp.mono_measure hmeasure,
      by simp, hgrad'⟩

end ESS

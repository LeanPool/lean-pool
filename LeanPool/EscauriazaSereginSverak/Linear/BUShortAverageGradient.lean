/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortExtendedEnergy
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellCylinderSpace
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# Gaussian average bounds for local gradient energy

A Gaussian averaging box dominates the outer Caccioppoli cylinder of a
short-time dyadic cell.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The Gaussian velocity average bounds gradient energy in the inner
Caccioppoli cylinder (`lem:bu-small-time`). -/
theorem bu_short_average_gradient_bound
    (X : Vec3) (δ c : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hc : 0 ≤ c)
    (hball : vec3Ball X (2 * (Real.sqrt δ / 8)) ⊆
      {x : Vec3 | 0 < x 2})
    (havgBall : vec3Ball X (Real.sqrt (3 * δ / 2)) ⊆
      {x : Vec3 | 0 < x 2})
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hcont : ContinuousOn v
      ({x : Vec3 | 0 < x 2} ×ˢ Ico (1 / 2 : ℝ) (3 / 2)))
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) (3 / 2)) v Dv D2v Dtv)
    (hlocal : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (1 / 2 : ℝ) (3 / 2)) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (1 / 2 : ℝ) (3 / 2)))),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c * (Real.sqrt (spatialGradientSq v Dv z) +
          vec3EuclideanNorm (v z))) :
    let r := Real.sqrt δ / 8
    let t := 1 / 2 + δ - r ^ 2 / 2
    let Avg := spaceTimeSet (vec3Ball X (Real.sqrt (3 * δ / 2)))
      (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
    (∫ z in spaceTimeSet (vec3Ball X r) (Ioo t (t + r ^ 2)),
      spatialGradientSq v Dv z ∂(volume : Measure ParabolicPoint)) ≤
      256 * (1 + c ^ 2 + 1 / r ^ 2) *
        (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
          ∂(volume : Measure ParabolicPoint)) := by
  dsimp
  let r := Real.sqrt δ / 8
  let t := 1 / 2 + δ - r ^ 2 / 2
  let Avg : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball X (Real.sqrt (3 * δ / 2)))
      (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
  let Out : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball X (2 * r)) (Ioo t (t + 4 * r ^ 2))
  have hr : 0 < r := by dsimp [r]; positivity
  have hAvgTime : Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4) ⊆
      Ioo (1 / 2 : ℝ) (3 / 2) := by
    intro s hs
    constructor
    · linarith only [hs.1, hδ]
    · linarith only [hs.2, hδhalf]
  have hOutAvg : Out ⊆ Avg := by
    intro z hz
    have hx := (bu_short_caccioppoli_outer_space_subset X δ hδ) hz.1
    have ht := (bu_short_caccioppoli_outer_time_subset δ hδ)
      (show z.2 - 1 / 2 ∈ Ioo (δ - r ^ 2 / 2)
        (δ - r ^ 2 / 2 + 4 * r ^ 2) by
        dsimp [Out, t] at hz
        constructor <;> linarith only [hz.2.1, hz.2.2])
    exact ⟨hx, ⟨by linarith only [ht.1], by linarith only [ht.2]⟩⟩
  have hOutTime : Ioo t (t + 4 * r ^ 2) ⊆
      Ioo (1 / 2 : ℝ) (3 / 2) := by
    intro s hs
    apply hAvgTime
    have ht := (bu_short_caccioppoli_outer_time_subset δ hδ)
      (show s - 1 / 2 ∈ Ioo (δ - r ^ 2 / 2)
        (δ - r ^ 2 / 2 + 4 * r ^ 2) by
        dsimp [t] at hs
        constructor <;> linarith only [hs.1, hs.2])
    exact ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  have hAvgSub : Avg ⊆
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (1 / 2 : ℝ) (3 / 2)) := by
    intro z hz
    exact ⟨havgBall hz.1, hAvgTime hz.2⟩
  have hAvgBound : Bornology.IsBounded Avg := by
    let B : Set Vec3 := vec3Ball X (Real.sqrt (3 * δ / 2))
    let K : Set ParabolicPoint := parabolicHomeomorph.symm ''
      (closure B ×ˢ Icc (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
    have hKcompact : IsCompact K := by
      exact ((isCompact_closure_vec3Ball (by positivity :
        0 < Real.sqrt (3 * δ / 2))).prod isCompact_Icc).image
        parabolicHomeomorph.symm.continuous
    apply hKcompact.isBounded.subset
    intro z hz
    refine ⟨(z.1, z.2), ⟨subset_closure hz.1, ?_⟩, ?_⟩
    · exact ⟨hz.2.1.le, hz.2.2.le⟩
    · apply parabolicHomeomorph.injective
      rw [parabolicHomeomorph.apply_symm_apply]
      rfl
  have hAvgInt : IntegrableOn
      (fun z => vec3EuclideanNorm (v z) ^ 2) Avg volume :=
    (bu_short_extended_energy_integrable_on hweak hlocal Avg
      hAvgSub hAvgBound).1
  have hOuterLe : (∫ z in Out, vec3EuclideanNorm (v z) ^ 2
        ∂(volume : Measure ParabolicPoint)) ≤
      (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
        ∂(volume : Measure ParabolicPoint)) := by
    apply setIntegral_mono_set hAvgInt
    · filter_upwards [] with z
      exact sq_nonneg _
    · exact ae_of_all _ hOutAvg
  have hCacc := bu_short_cell_caccioppoli X t r c hr hc
    (by simpa only [r] using hball) hOutTime
    hcont hweak hlocal hineq
  exact hCacc.trans (mul_le_mul_of_nonneg_left hOuterLe (by positivity))

end ESS

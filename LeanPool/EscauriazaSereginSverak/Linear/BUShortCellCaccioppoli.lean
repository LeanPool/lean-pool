/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortExtendedGrowth
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortUCSpatialRestriction
public import LeanPool.EscauriazaSereginSverak.Linear.Caccioppoli
public import LeanPool.EscauriazaSereginSverak.Linear.UCRestriction
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import Mathlib.Topology.Bornology.Constructions

/-!
# Local energy on an extended short-time cell

The Caccioppoli estimate applies to a bounded cylinder inside
the extended rescaled half-space domain.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Caccioppoli bounds the inner gradient energy on any enlarged cell
inside the extended short-time cylinder (`lem:caccioppoli`). -/
theorem bu_short_cell_caccioppoli
    (X : Vec3) (t r c : ℝ) (hr : 0 < r) (hc : 0 ≤ c)
    (hball : vec3Ball X (2 * r) ⊆ {x : Vec3 | 0 < x 2})
    (htime : Ioo t (t + 4 * r ^ 2) ⊆ Ioo (1 / 2 : ℝ) (3 / 2))
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
    (∫ z in spaceTimeSet (vec3Ball X r) (Ioo t (t + r ^ 2)),
      spatialGradientSq v Dv z ∂(volume : Measure ParabolicPoint)) ≤
      256 * (1 + c ^ 2 + 1 / r ^ 2) *
        (∫ z in spaceTimeSet (vec3Ball X (2 * r))
          (Ioo t (t + 4 * r ^ 2)),
          vec3EuclideanNorm (v z) ^ 2
          ∂(volume : Measure ParabolicPoint)) := by
  let B : Set Vec3 := vec3Ball X (2 * r)
  let I : Set ℝ := Ioo (1 / 2 : ℝ) (3 / 2)
  let J : Set ℝ := Ioo t (t + 4 * r ^ 2)
  have hBopen : IsOpen B := isOpen_vec3Ball X (2 * r)
  have hUbound : Bornology.IsBounded (spaceTimeSet B I) := by
    let K : Set ParabolicPoint := parabolicHomeomorph.symm ''
      (closure B ×ˢ Icc (1 / 2 : ℝ) (3 / 2))
    have hKcompact : IsCompact K := by
      exact ((isCompact_closure_vec3Ball (mul_pos (by norm_num) hr)).prod
        isCompact_Icc).image parabolicHomeomorph.symm.continuous
    apply hKcompact.isBounded.subset
    intro z hz
    refine ⟨(z.1, z.2), ⟨subset_closure hz.1, ?_⟩, ?_⟩
    · exact ⟨hz.2.1.le, hz.2.2.le⟩
    · apply parabolicHomeomorph.injective
      rw [parabolicHomeomorph.apply_symm_apply]
      rfl
  have hUsub : spaceTimeSet B I ⊆
      spaceTimeSet {x : Vec3 | 0 < x 2} I := by
    intro z hz
    exact ⟨hball hz.1, hz.2⟩
  have hL2 : (∫⁻ z in spaceTimeSet B I,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    hlocal _ hUsub hUbound
  have hweakB := bu_weak_restrict_space_interval measurableSet_Ioo
    hball v Dv D2v Dtv hweak
  have hcontB : ContinuousOn v (B ×ˢ I) := by
    apply hcont.mono
    intro z hz
    exact ⟨hball hz.1, hz.2.1.le, hz.2.2⟩
  have hineqB : ∀ᵐ z ∂(volume.restrict (spaceTimeSet B I)),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c * (vec3EuclideanNorm (v z) +
          Real.sqrt (spatialGradientSq v Dv z)) := by
    have h := ae_restrict_of_ae_restrict_of_subset hUsub hineq
    filter_upwards [h] with z hz
    convert hz using 1; ring
  have hrestricted := uc_restrict_data c B B J I
    v Dv D2v Dtv hBopen isOpen_Ioo (subset_refl B) htime
    hcontB hweakB hL2 hineqB
  exact caccioppoli X t r c hr hc hrestricted.2.1
    hrestricted.2.2.1 hrestricted.2.2.2

end ESS

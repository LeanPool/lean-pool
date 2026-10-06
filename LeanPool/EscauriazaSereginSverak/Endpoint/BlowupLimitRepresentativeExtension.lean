/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitTraceField

/-!
# Zero extensions of the all-time trace representative

The jointly measurable representative can be zero-extended from its closed
source cylinder and then rescaled as a measurable field on all of space-time.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The all-time trace representative, extended by zero outside its closed
source cylinder. -/
@[expose] def blowupLimitTraceZeroExtension
    {a b : ℝ} (W : Vec3 × Icc a b → Vec3) : ParabolicPoint → Vec3 := by
  classical
  exact fun z => if hz : z.1 ∈ vec3Ball 0 (3 / 4 : ℝ) ∧ z.2 ∈ Icc a b then
    W (z.1, ⟨z.2, hz.2⟩) else 0

/-- The zero extension of a jointly measurable trace representative is
measurable on the full space-time carrier. -/
theorem measurable_blowupLimitTraceZeroExtension
    {a b : ℝ} (W : Vec3 × Icc a b → Vec3) (hW : Measurable W) :
    Measurable (blowupLimitTraceZeroExtension W) := by
  classical
  let J : Set ParabolicPoint := vec3Ball 0 (3 / 4 : ℝ) ×ˢ Icc a b
  have hJ : MeasurableSet J :=
    (isOpen_vec3Ball 0 (3 / 4 : ℝ)).measurableSet.prod measurableSet_Icc
  have hmap : Measurable (fun z : J =>
      (z.1.1, (⟨z.1.2, z.2.2⟩ : Icc a b))) := by
    apply (measurable_fst.comp measurable_subtype_coe).prodMk
    have htime : Measurable (fun z : J => z.1.2) :=
      measurable_snd.comp measurable_subtype_coe
    exact htime.subtype_mk (h := fun z : J => z.2.2)
  have hOnEq : J.domRestrict
      (blowupLimitTraceZeroExtension W) = fun z : J =>
        W (z.1.1, (⟨z.1.2, z.2.2⟩ : Icc a b)) := by
    funext z
    change (if hz : z.1.1 ∈ vec3Ball 0 (3 / 4 : ℝ) ∧
      z.1.2 ∈ Icc a b then W (z.1.1, ⟨z.1.2, hz.2⟩) else 0) = _
    have hz : z.1.1 ∈ vec3Ball 0 (3 / 4 : ℝ) ∧ z.1.2 ∈ Icc a b := z.2
    simp [hz]
  have hOn : Measurable (J.domRestrict
      (blowupLimitTraceZeroExtension W)) := by
    rw [hOnEq]
    exact hW.comp hmap
  have hOff : Measurable ((Set.compl J).domRestrict
      (blowupLimitTraceZeroExtension W)) := by
    have hOffEq : (Set.compl J).domRestrict
        (blowupLimitTraceZeroExtension W) = fun _ : (Set.compl J) => (0 : Vec3) := by
      funext z
      change (if hz : z.1.1 ∈ vec3Ball 0 (3 / 4 : ℝ) ∧
        z.1.2 ∈ Icc a b then W (z.1.1, ⟨z.1.2, hz.2⟩) else 0) = 0
      have hz : ¬ (z.1.1 ∈ vec3Ball 0 (3 / 4 : ℝ) ∧ z.1.2 ∈ Icc a b) := by
        intro hz
        exact z.2 ⟨hz.1, hz.2⟩
      by_cases h : z.1.1 ∈ vec3Ball 0 (3 / 4 : ℝ) ∧ z.1.2 ∈ Icc a b
      · exact (hz h).elim
      · rw [dite_eq_right h]
    rw [hOffEq]
    exact measurable_const
  exact measurable_of_restrict_of_restrict_compl hJ hOn hOff

/-- Parabolically rescale the measurable, zero-extended all-time trace. -/
@[expose] def blowupLimitTraceRescaling
    {a b : ℝ} (W : Vec3 × Icc a b → Vec3)
    (x₀ : Vec3) (t₀ r : ℝ) : ParabolicPoint → Vec3 :=
  fun z => r • blowupLimitTraceZeroExtension W
    (parabolicTranslate x₀ t₀ (parabolicScale r z))

/-- Every rescaling of the zero-extended trace is jointly measurable. -/
theorem measurable_blowupLimitTraceRescaling
    {a b : ℝ} (W : Vec3 × Icc a b → Vec3) (hW : Measurable W)
    (x₀ : Vec3) (t₀ r : ℝ) :
    Measurable (blowupLimitTraceRescaling W x₀ t₀ r) := by
  have hbase := measurable_blowupLimitTraceZeroExtension W hW
  have hsmul : Measurable (fun y : Vec3 => r • y) :=
    (continuous_const_smul r).measurable
  have hspace : Measurable (fun z : ParabolicPoint => x₀ + r • z.1) :=
    measurable_const.add (measurable_fst.const_smul r)
  have htime : Measurable (fun z : ParabolicPoint => t₀ + r ^ 2 * z.2) :=
    measurable_const.add (measurable_const.mul measurable_snd)
  have hchange : Measurable (fun z : ParabolicPoint =>
      (x₀ + r • z.1, t₀ + r ^ 2 * z.2)) := hspace.prodMk htime
  change Measurable ((fun y : Vec3 => r • y) ∘
    (blowupLimitTraceZeroExtension W) ∘
    (fun z : ParabolicPoint => (x₀ + r • z.1, t₀ + r ^ 2 * z.2)) )
  exact hsmul.comp (hbase.comp hchange)

end ESS

end

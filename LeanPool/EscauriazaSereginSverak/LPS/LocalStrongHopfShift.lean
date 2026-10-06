/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongEnergy
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Time translation of a strong solution

Translating a space-time field in time by `t₀` preserves the slab measure, the
space-time test-function class, and the spatial and time partial derivatives
of the translated tests (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The translation of the time variable by `t₀`. -/
@[expose] def lpsShift (t₀ : ℝ) (z : ParabolicPoint) : ParabolicPoint := (z.1, t₀ + z.2)

/-- The time translation carries the slab over `(a, b)` measure preservingly
onto the slab over `(t₀ + a, t₀ + b)`. -/
theorem lps_shift_measurePreserving (t₀ a b : ℝ) :
    MeasurePreserving (lpsShift t₀)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + a) (t₀ + b)))) := by
  let e : ParabolicPoint ≃ᵐ ParabolicPoint :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl Vec3) (MeasurableEquiv.addLeft t₀)
  have hmp : MeasurePreserving e volume volume := by
    have h1 : MeasurePreserving (Prod.map (id : Vec3 → Vec3) (fun t : ℝ => t₀ + t))
        ((volume : Measure Vec3).prod (volume : Measure ℝ))
        ((volume : Measure Vec3).prod (volume : Measure ℝ)) :=
      (MeasurePreserving.id (volume : Measure Vec3)).prod (measurePreserving_add_left volume t₀)
    exact h1
  have himage : e '' spaceTimeSet (Set.univ : Set Vec3) (Ioo a b) =
      spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + a) (t₀ + b)) := by
    change Prod.map (id : Vec3 → Vec3) (fun t : ℝ => t₀ + t) '' ((Set.univ : Set Vec3) ×ˢ Ioo a b) =
      (Set.univ : Set Vec3) ×ˢ Ioo (t₀ + a) (t₀ + b)
    rw [Set.prodMap_image_prod, Set.image_id, Set.image_const_add_Ioo]
  have hmp' := hmp.restrict_image_emb e.measurableEmbedding
    (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))
  rw [himage] at hmp'
  exact hmp'

/-- The spatial partial derivative of a time-translated function. -/
theorem lps_shift_spatialPartial (t₀ : ℝ) (g : ParabolicPoint → ℝ) (j : Fin 3)
    (z : ParabolicPoint) :
    spatialPartial (fun y : ParabolicPoint => g (y.1, y.2 - t₀)) j (lpsShift t₀ z) =
      spatialPartial g j z := by
  unfold spatialPartial lpsShift
  simp only [add_sub_cancel_left]

/-- The time partial derivative of a time-translated function. -/
theorem lps_shift_timePartial (t₀ : ℝ) (g : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    timePartial (fun y : ParabolicPoint => g (y.1, y.2 - t₀)) (lpsShift t₀ z) =
      timePartial g z := by
  unfold timePartial lpsShift
  simp only
  rw [fderiv_apply_one_eq_deriv, fderiv_apply_one_eq_deriv]
  have h := deriv_comp_sub_const (f := fun s : ℝ => g (z.1, s)) (a := t₀) (x := t₀ + z.2)
  simp only [add_sub_cancel_left] at h
  exact h

/-- A vector-valued space-time test field, translated in time. -/
theorem lps_shift_testFunction {a b : ℝ} (t₀ : ℝ) {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a b)) :
    (fun y : Vec3 × ℝ => φ (y.1, y.2 - t₀)) ∈
      spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo (t₀ + a) (t₀ + b)) := by
  obtain ⟨hd, hc, hs⟩ := hφ
  let h : Vec3 × ℝ ≃ₜ Vec3 × ℝ := (Homeomorph.refl Vec3).prodCongr (Homeomorph.subRight t₀)
  have hfun : (fun y : Vec3 × ℝ => φ (y.1, y.2 - t₀)) = φ ∘ h := rfl
  refine ⟨hd.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)),
    ?_, ?_⟩
  · rw [hfun]
    exact hc.comp_homeomorph h
  · rw [hfun, tsupport_comp_eq_preimage φ h]
    intro y hy
    have h1 : h y ∈ Set.univ ×ˢ Ioo a b := hs hy
    have h2 : y.2 - t₀ ∈ Ioo a b := h1.2
    exact ⟨mem_univ _, by linarith only [h2.1], by linarith only [h2.2]⟩

theorem lps_shift_measurableEmbedding (t₀ : ℝ) : MeasurableEmbedding (lpsShift t₀) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Vec3)
    (MeasurableEquiv.addLeft t₀)).measurableEmbedding

end ESS.LPS

end

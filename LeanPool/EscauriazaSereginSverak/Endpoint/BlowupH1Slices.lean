/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupEnergyPressureSource
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.VelocityTenThirds

/-!
# Blowup H1 Slices

Spatial Sobolev slice bounds for the rescaled endpoint sequence.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- A measurable field with finite squared energy belongs to local `L²`. -/
theorem blowup_memLp_two_of_energy
    {E : Type*} [NormedAddCommGroup E]
    {S : Set ParabolicPoint} {v : ParabolicPoint → E}
    (hv : AEStronglyMeasurable v (volume.restrict S))
    (hfinite : (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤) :
    MemLp v 2 (volume.restrict S) := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by finiteness : (2 : ℝ≥0∞) ≠ ⊤) hv]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfinite.ne

private theorem blowup_slice_memLp_two_ae_of_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J) :
    ∀ᵐ s ∂volume.restrict J,
      MemLp (fun x : Vec3 => u (x,s)) 2 (volume.restrict Ω') ∧
      MemLp (fun x : Vec3 => Du (x,s)) 2 (volume.restrict Ω') := by
  let S := spaceTimeSet Ω' J
  have hu := hdata.aestronglyMeasurable_velocity hbox
  have hDu := hdata.aestronglyMeasurable_gradient hbox
  have henergy := hdata.energy_lintegral_lt_top hbox
  have hu_lt : (∫⁻ z in S, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (lintegral_mono (fun _ => le_add_right le_rfl)).trans_lt henergy
  have hDu_lt : (∫⁻ z in S, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (lintegral_mono (fun _ => le_add_left le_rfl)).trans_lt henergy
  have hu2 := blowup_memLp_two_of_energy hu hu_lt
  have hDu2 := blowup_memLp_two_of_energy hDu hDu_lt
  have hu_sq : Integrable (fun z => (‖u z‖ : ℝ) ^ (2 : ℕ))
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hu2.integrable_norm_pow (by norm_num)
  have hDu_sq : Integrable (fun z => (‖Du z‖ : ℝ) ^ (2 : ℕ))
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hDu2.integrable_norm_pow (by norm_num)
  have hu_meas : AEStronglyMeasurable u
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hu
  have hDu_meas : AEStronglyMeasurable Du
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hDu
  filter_upwards [hu_meas.prodMk_right, hDu_meas.prodMk_right,
    hu_sq.prod_left_ae, hDu_sq.prod_left_ae]
    with s hus hDus husq hDusq
  exact ⟨(memLp_two_iff_integrable_sq_norm hus).2 husq,
    (memLp_two_iff_integrable_sq_norm hDus).2 hDusq⟩

/-- Each component of a suitable velocity has an H¹ representative on almost
every spatial ball slice of a local box. -/
theorem blowup_h1_slices_of_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    {x₀ : Vec3} {r : ℝ} (hball : vec3Ball x₀ r ⊆ Ω') (i : Fin 3) :
    ∀ᵐ s ∂volume.restrict J, ∃ v : H1Function (vec3Ball x₀ r),
      (fun x => u (x,s) i) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.toFun ∧
      (fun x => Du (x,s) i) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.grad := by
  filter_upwards [blowup_slice_memLp_two_ae_of_data hdata hbox,
    hdata.hasWeakGradientOn_slice hbox i] with s hmem hgrad
  refine ⟨⟨fun x => u (x,s) i, fun x => Du (x,s) i, ?_, fun j => ?_, ?_⟩,
    Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
  · exact (memLp_pi_iff.mp hmem.1 i).mono_measure
      (Measure.restrict_mono hball le_rfl)
  · exact (memLp_pi_iff.mp (memLp_pi_iff.mp hmem.2 i) j).mono_measure
      (Measure.restrict_mono hball le_rfl)
  · exact hgrad.restrict (isOpen_vec3Ball x₀ r) hball

end ESS

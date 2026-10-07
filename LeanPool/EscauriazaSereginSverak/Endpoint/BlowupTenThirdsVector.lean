/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTenThirds

/-!
# Blowup Ten Thirds Vector

Space-time integrability of the rescaled velocity at exponent 10/3.
-/

public section

open MeasureTheory CKN.Foundation.Parabolic
open scoped ENNReal
namespace ESS

/-- Inserting one scalar component into a vector preserves its `Lᵖ` norm. -/
theorem blowup_single_eLpNorm_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : ℝ≥0∞) (i : Fin 3) (f : α → ℝ)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun z => (Pi.single i (f z) : Vec3)) p μ = eLpNorm f p μ := by
  classical
  have hcont : Continuous (fun y : ℝ => (Pi.single i y : Vec3)) :=
    (Isometry.single (E := fun _ : Fin 3 => ℝ) i).continuous
  have hsingle : AEStronglyMeasurable (fun z => (Pi.single i (f z) : Vec3)) μ :=
    hcont.comp_aestronglyMeasurable hf
  have henorm (z : α) : ‖(Pi.single i (f z) : Vec3)‖ₑ = ‖f z‖ₑ :=
    Pi.enorm_single (G := fun _ : Fin 3 => ℝ) (f z)
  exact eLpNorm_congr_enorm_ae (p := p) (μ := μ)
    (f := fun z => (Pi.single i (f z) : Vec3)) (g := f)
    hsingle hf (Filter.Eventually.of_forall henorm)

/-- The `Lᵖ` norm of a three component field is bounded by the sum of the
component norms. -/
theorem blowup_vec3_eLpNorm_le_sum_components
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (f : α → Vec3)
    (hf : ∀ i : Fin 3, MemLp (fun z => f z i) p μ) :
    eLpNorm f p μ ≤ ∑ i : Fin 3, eLpNorm (fun z => f z i) p μ := by
  classical
  have hdecomp : f = ∑ i : Fin 3, (fun z => (Pi.single i (f z i) : Vec3)) := by
    ext z j
    simp
  calc
    eLpNorm f p μ =
        eLpNorm (∑ i : Fin 3, (fun z => (Pi.single i (f z i) : Vec3))) p μ :=
      congrArg (fun g : α → Vec3 => eLpNorm g p μ) hdecomp
    _ ≤
        ∑ i : Fin 3, eLpNorm (fun z => (Pi.single i (f z i) : Vec3)) p μ :=
      eLpNorm_sum_le (μ := μ) (p := p)
        (s := Finset.univ)
        (f := fun i : Fin 3 => fun z : α => (Pi.single i (f z i) : Vec3)) hp
    _ = ∑ i : Fin 3, eLpNorm (fun z => f z i) p μ := by
      simp_rw [blowup_single_eLpNorm_eq μ p _ _ (hf _).aestronglyMeasurable]

/-- Uniform bounds for the three scalar velocity components give a uniform
bound for the vector field in the product norm. -/
theorem blowup_uniform_vec3Lp_of_components
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (f : ℕ → α → Vec3)
    (hbound : ∀ i : Fin 3, ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ k, eLpNorm (fun z => f k z i) p μ ≤ B) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ k, eLpNorm (f k) p μ ≤ B := by
  classical
  choose C hC hCbound using hbound
  let B := ∑ i : Fin 3, C i
  have hB : B < ⊤ := ENNReal.sum_lt_top.mpr (fun i _ => hC i)
  refine ⟨B, hB, ?_⟩
  intro k
  have hf : ∀ i : Fin 3, MemLp (fun z => f k z i) p μ := by
    intro i
    rw [memLp_iff]
    exact lt_of_le_of_lt (hCbound i k) (hC i)
  calc
    eLpNorm (f k) p μ ≤ ∑ i : Fin 3, eLpNorm (fun z => f k z i) p μ :=
      blowup_vec3_eLpNorm_le_sum_components μ p hp (f k) hf
    _ ≤ B := Finset.sum_le_sum (fun i _ => hCbound i k)

end ESS

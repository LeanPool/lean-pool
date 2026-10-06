/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityDivergenceSupport
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalFinite
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Stability Divergence Sum

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The divergence pairing on a local box is the finite sum of its
coordinate pairings when the velocity is locally `L³`. -/
theorem stability_divergence_sum_integral_eq
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (hbox : localBox Ω I Ω' J)
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (f : ParabolicPoint → Vec3)
    (hf : MemLp f 3 (volume.restrict (spaceTimeSet Ω' J))) :
    (∫ z in spaceTimeSet Ω' J,
      ∑ i : Fin 3, f z i * spatialPartial ψ i z) =
      ∑ i : Fin 3, ∫ z in spaceTimeSet Ω' J,
        spatialPartial ψ i z * f z i := by
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let _ : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have hterm (i : Fin 3) : Integrable
      (fun z : ParabolicPoint => f z i * spatialPartial ψ i z) μ := by
    have hfi3 : MemLp (fun z => f z i) 3 μ := (memLp_pi_iff.mp hf) i
    have hfi1 : Integrable (fun z => f z i) μ :=
      memLp_one_iff_integrable.mp (hfi3.mono_exponent (by norm_num))
    have htestCont : Continuous
        (fun z : ParabolicPoint => spatialPartial ψ i z) :=
      (spatialPartial_contDiff hψ.1 i).continuous.comp
        parabolicHomeomorph.continuous
    obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hψ i
    have htest : MemLp (fun z : ParabolicPoint => spatialPartial ψ i z) ∞ μ :=
      memLp_top_of_bound htestCont.aestronglyMeasurable C
        (Eventually.of_forall fun z => hC (parabolicHomeomorph z))
    have heq :
        (fun z : ParabolicPoint => f z i * spatialPartial ψ i z) =
        (fun z => f z i) * (fun z => spatialPartial ψ i z) := by
      funext z
      rfl
    rw [heq]
    exact hfi1.mul_of_top_left htest
  rw [integral_finsetSum _ (fun i _ => hterm i)]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with z
  ring

end CKN

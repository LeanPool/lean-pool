/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilitySliceEnergySpaceTime
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalVelocityLp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Stability S1Slice

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- Strong local `L³` convergence preserves the uniform time-slice energy bound
of suitable solutions (`thm:stability`). -/
theorem stability_suitable_limit_slice_energy_lt_top
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (hsol : ∀ n, CKN.IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hbox : CKN.localBox Ω I Ω' J)
    (hconv : Tendsto
      (fun n => eLpNorm (u n - v) 3
        (volume.restrict (CKN.spaceTimeSet Ω' J))) atTop (nhds 0))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hbound : ∀ n,
      essSup (fun t => ∫⁻ x in Ω', ‖u n (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict J) ≤ M) :
    essSup (fun t => ∫⁻ x in Ω', ‖v (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict J) < ⊤ := by
  let μ : Measure Vec3 := volume.restrict Ω'
  let ν : Measure ℝ := volume.restrict J
  have hmeasure : μ.prod ν =
      (volume : Measure (Vec3 × ℝ)).restrict (Ω' ×ˢ J) := by
    dsimp [μ, ν]
    rw [Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  have hfn (n : ℕ) : MemLp (u n) 3
      (volume.restrict (CKN.spaceTimeSet Ω' J)) :=
    stability_velocity_memLp_three_on_localBox (hsol n) hbox
  have hv : MemLp v 3 (volume.restrict (CKN.spaceTimeSet Ω' J)) :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) hfn v hconv
  have hS : MeasurableSet (CKN.spaceTimeSet Ω' J) :=
    hbox.1.measurableSet.prod hbox.2.2.2.1.measurableSet
  have hpre : parabolicHomeomorph.symm ⁻¹' CKN.spaceTimeSet Ω' J =
      Ω' ×ˢ J := by ext z; rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hS
  rw [hpre] at hmp
  have hfnprod (n : ℕ) : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => u n (z.1, z.2)) (μ.prod ν) := by
    have h := (hfn n).comp_measurePreserving hmp
    change MemLp (fun z : Vec3 × ℝ => u n (z.1, z.2)) 3
      (volume.restrict (Ω' ×ˢ J)) at h
    rw [hmeasure]
    exact h.aestronglyMeasurable
  have hvprod : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => v (z.1, z.2)) (μ.prod ν) := by
    have h := hv.comp_measurePreserving hmp
    change MemLp (fun z : Vec3 × ℝ => v (z.1, z.2)) 3
      (volume.restrict (Ω' ×ˢ J)) at h
    rw [hmeasure]
    exact h.aestronglyMeasurable
  have hconvprod : Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => u n (z.1, z.2) - v (z.1, z.2)) 3 (μ.prod ν))
      atTop (nhds 0) := by
    have heq (n : ℕ) : eLpNorm
        (fun z : Vec3 × ℝ => u n (z.1, z.2) - v (z.1, z.2)) 3 (μ.prod ν) =
        eLpNorm (u n - v) 3
          (volume.restrict (CKN.spaceTimeSet Ω' J)) := by
      have h := eLpNorm_comp_measurePreserving (p := (3 : ℝ≥0∞))
        ((hfn n).aestronglyMeasurable.sub hv.aestronglyMeasurable) hmp
      change eLpNorm
        (fun z : Vec3 × ℝ => u n (z.1, z.2) - v (z.1, z.2)) 3
          (volume.restrict (Ω' ×ˢ J)) = _ at h
      rwa [hmeasure]
    simpa only [heq] using hconv
  exact stability_essSup_slice_energy_lt_top_spaceTime μ ν
    (fun n z => u n (z.1, z.2)) (fun z => v (z.1, z.2))
    hfnprod hvprod hconvprod M hM hbound

end CKN

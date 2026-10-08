/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalFinite
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# Stability Local Product Lp

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- Strong convergence on a CKN local box agrees with strong convergence in
its ordinary product coordinates. -/
theorem stability_eLpNorm_tendsto_localBox_prod
    {E : Type*} [NormedAddCommGroup E]
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (hbox : CKN.localBox Ω I Ω' J)
    (r : ℝ≥0∞) (F : ℕ → ParabolicPoint → E) (G : ParabolicPoint → E)
    (hF : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (CKN.spaceTimeSet Ω' J)))
    (hG : AEStronglyMeasurable G
      (volume.restrict (CKN.spaceTimeSet Ω' J)))
    (hconv : Tendsto (fun n => eLpNorm (F n - G) r
      (volume.restrict (CKN.spaceTimeSet Ω' J))) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => F n (z.1, z.2) - G (z.1, z.2)) r
      ((volume.restrict Ω').prod (volume.restrict J)))
      atTop (nhds 0) := by
  have hS : MeasurableSet (CKN.spaceTimeSet Ω' J) :=
    hbox.1.measurableSet.prod hbox.2.2.2.1.measurableSet
  have hpre : parabolicHomeomorph.symm ⁻¹' CKN.spaceTimeSet Ω' J =
      Ω' ×ˢ J := by ext z; rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hS
  rw [hpre] at hmp
  have hmeasure : (volume.restrict Ω').prod (volume.restrict J) =
      (volume : Measure (Vec3 × ℝ)).restrict (Ω' ×ˢ J) := by
    rw [Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  have heq (n : ℕ) : eLpNorm
      (fun z : Vec3 × ℝ => F n (z.1, z.2) - G (z.1, z.2)) r
      ((volume.restrict Ω').prod (volume.restrict J)) =
      eLpNorm (F n - G) r
        (volume.restrict (CKN.spaceTimeSet Ω' J)) := by
    have h := eLpNorm_comp_measurePreserving (p := r)
      ((hF n).sub hG) hmp
    change eLpNorm
      (fun z : Vec3 × ℝ => F n (z.1, z.2) - G (z.1, z.2)) r
      (volume.restrict (Ω' ×ˢ J)) = _ at h
    rwa [hmeasure]
  simpa only [heq] using hconv

end CKN

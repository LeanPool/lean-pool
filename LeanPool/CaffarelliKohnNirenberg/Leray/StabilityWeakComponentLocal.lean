/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalProductMemLp
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalProductIntegral

/-!
# Stability Weak Component Local

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- Componentwise weak `L²` convergence in product coordinates transfers to
CKN local-box integrals. -/
theorem stability_weak_component_localBox
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (hbox : localBox Ω I Ω' J)
    (D : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (d : ParabolicPoint → Fin 3 → Vec3)
    (hweak : ∀ i j : Fin 3, ∀ w : Vec3 × ℝ → ℝ,
      MemLp w 2 ((volume.restrict Ω').prod (volume.restrict J)) →
      Tendsto (fun n => ∫ z, D n (z.1, z.2) i j * w z
        ∂(volume.restrict Ω').prod (volume.restrict J)) atTop
        (nhds (∫ z, d (z.1, z.2) i j * w z
          ∂(volume.restrict Ω').prod (volume.restrict J))))
    (i j : Fin 3) (w : ParabolicPoint → ℝ)
    (hw : MemLp w 2 (volume.restrict (spaceTimeSet Ω' J))) :
    Tendsto (fun n => ∫ z in spaceTimeSet Ω' J, D n z i j * w z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J, d z i j * w z)) := by
  have hwProd := stability_memLp_localBox_prod hbox hw
  have h := hweak i j _ hwProd
  have heqFn (n : ℕ) :
      (∫ z in spaceTimeSet Ω' J, D n z i j * w z) =
      ∫ z : Vec3 × ℝ, D n (z.1, z.2) i j * w (z.1, z.2)
        ∂((volume.restrict Ω').prod (volume.restrict J)) :=
    stability_setIntegral_localBox_eq_prod _
  have heqG :
      (∫ z in spaceTimeSet Ω' J, d z i j * w z) =
      ∫ z : Vec3 × ℝ, d (z.1, z.2) i j * w (z.1, z.2)
        ∂((volume.restrict Ω').prod (volume.restrict J)) :=
    stability_setIntegral_localBox_eq_prod _
  simpa only [heqFn, heqG] using h

end CKN
